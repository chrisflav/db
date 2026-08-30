/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import SQLite.LowLevel
import Db.Backends.Sql
import Db.Interpretation.Basic
import Db.Model

/-!
# SQLite backend

This module provides a database backend backed by [`leansqlite`](https://github.com/leanprover/leansqlite),
the official Lean bindings for SQLite. It mirrors the PostgreSQL backend: the typed queries are
turned into SQL strings by `Db.Backends.Sql` and executed through the SQLite C bindings.

The backend runs in the `Sqlite.M` monad, a thin reader over an open `SQLite` connection. Because
SQLite is embedded (the amalgamation is bundled by `leansqlite`), no external database server is
required and databases can be in-memory (`":memory:"`) or file-backed.

Two things differ from PostgreSQL and are handled here:

* Schema introspection uses `sqlite_master` joined with `pragma_table_info`, rather than
  `information_schema.columns` (which SQLite does not have).
* `ALTER TABLE` in SQLite supports only one change per statement and cannot change a column's type or
  nullability at all. So `execute` emits one statement per add/drop/rename command, and realises a
  type or nullability change by rebuilding the table (create a new table with the target schema, copy
  the data over, drop the old table, and rename the new one into place) inside a transaction.
-/

namespace Sqlite

open scoped SQLite

/-- The SQLite backend monad: a reader over an open connection. Errors surface as `IO` exceptions. -/
abbrev M := ReaderT SQLite IO

/-- Run a SQLite computation against the database at `path` (use `":memory:"` for an in-memory
database), opening the connection first. -/
def runDB (path : System.FilePath) {α : Type} (x : M α) : IO α := do
  let db ← SQLite.open path
  x.run db

/-- Run a `SELECT` statement and return the resulting rows, each as a map from (aliased) column
name to its textual value. This matches the representation the query interpretation expects: values
are decoded from strings via `FromString`, exactly as in the PostgreSQL backend. -/
def query (sql : String) : M (Array (Std.HashMap String String)) := do
  let db ← read
  let stmt ← db.prepare sql
  let ncols := stmt.columnCount.toNat
  let mut rows : Array (Std.HashMap String String) := #[]
  while (← stmt.step) do
    let mut row : Std.HashMap String String := ∅
    for i in [0:ncols] do
      let name ← stmt.columnName (Int32.ofNat i)
      let val ← stmt.columnText (Int32.ofNat i)
      row := row.insert name val
    rows := rows.push row
  return rows

instance (d : Database) : DBMonad d M where
  lookup {view} q := do
    let sql : SQL.Select := .fromQuery q
    let rows ← query sql.toString
    rows.filterMapM fun row => do
      return .mk <$> Enum.fromHashMap? (← do
        let mut map := default
        for idx in Enum.all view.Index do
          if h : s!"{idx}" ∈ row then
            match (FromString.fromString row[s!"{idx}"] :
                Option (view.name idx).column.Value) with
            | some val => map := map.insert idx val
            | none => pure ()
          else
            pure ()
        return map)
  insert {table} data := do
    let db ← read
    let sql : SQL.Insert := .fromInsert data
    db.exec sql.toString
  delete {view} e := do
    let db ← read
    match SQL.Delete.fromCondition e with
    | some del =>
      db.exec del.toString
      -- `changes` reports the number of rows affected by the last `DELETE`.
      return (← db.changes).toInt.toNat
    | none =>
      throw <| IO.userError <|
        "SQLite backend: `delete` requires a condition over a single table; " ++
        "the given view references columns from multiple tables."

/-- Parse a SQLite declared column type back into a `DBType`. SQLite preserves the declared type
string, so the types emitted by `DBType.toString` (`integer`, `varchar(n)`, `bool`) round-trip. -/
def parseDBType (s : String) : Option DBType :=
  let low := s.toLower
  if low == "integer" || low == "int" then
    some .int
  else if low == "bool" || low == "boolean" then
    some .bool
  else if low.startsWith "varchar" || low.startsWith "text" then
    match low.splitOn "(" with
    | [_, rest] =>
      match rest.splitOn ")" with
      | n :: _ => some (.varchar (n.toNat?.getD 0))
      | _ => some (.varchar 0)
    | _ => some (.varchar 255)
  else
    none

/-- A column as tracked while rebuilding a table: `(name, declared type, NOT NULL, source name)`.
`source` is the column's name in the *existing* table (used to copy its data across the rebuild) or
`none` for a freshly added column, which has no data to preserve. -/
abbrev RebuildColumn := String × String × Bool × Option String

/-- Introspect the current columns of `tableName`, in definition order, as `RebuildColumn`s whose
`source` is their own name (they all exist and their data must be preserved). -/
def currentColumns (tableName : String) : M (Array RebuildColumn) := do
  let rows ← query
    s!"SELECT name AS nm, type AS ty, [notnull] AS nn FROM pragma_table_info('{tableName}') ORDER BY cid"
  return rows.filterMap fun row =>
    match row.get? "nm", row.get? "ty" with
    | some n, some ty => some (n, ty, row.getD "nn" "0" == "1", some n)
    | _, _ => none

open SQL.Migration in
/-- Apply one `ALTER TABLE` command to the working column list of a table rebuild. -/
def applyAlterCommand (cols : Array RebuildColumn) : AlterTableCommand → Array RebuildColumn
  | .addColumn field => cols.push (field.name, field.type, !field.nullable, none)
  | .dropColumn name => cols.filter fun (n, _, _, _) => n != name
  | .renameColumn old new =>
    cols.map fun (n, ty, nn, src) => if n == old then (new, ty, nn, src) else (n, ty, nn, src)
  | .alterColumn name (.setType ty) =>
    cols.map fun (n, t, nn, src) => if n == name then (n, ty, nn, src) else (n, t, nn, src)
  | .alterColumn name (.setNullable nullable) =>
    cols.map fun (n, t, nn, src) => if n == name then (n, t, !nullable, src) else (n, t, nn, src)

open SQL.Migration in
/-- Rebuild `tableName` to the schema obtained by applying `commands` to its current columns. SQLite
does not support `ALTER COLUMN`, so type and nullability changes are realised by the standard
create/copy/drop/rename dance, run inside a transaction so it is all-or-nothing. -/
def rebuildTable (tableName : String) (commands : List AlterTableCommand) : M Unit := do
  let db ← read
  let current ← currentColumns tableName
  let newCols := commands.foldl applyAlterCommand current
  let fieldDefs := newCols.toList.map fun (n, ty, nn, _) =>
    s!"{n} {ty}{if nn then " NOT NULL" else ""}"
  -- Columns present both before and after keep their data; match old name → new name.
  let copyPairs := newCols.toList.filterMap fun (n, _, _, src) => src.map (·, n)
  let newNames := ", ".intercalate (copyPairs.map (·.2))
  let oldNames := ", ".intercalate (copyPairs.map (·.1))
  let tmp := s!"__db_migrate_{tableName}"
  db.transaction do
    db.exec s!"CREATE TABLE {tmp} (\n  {",\n  ".intercalate fieldDefs}\n)"
    unless copyPairs.isEmpty do
      db.exec s!"INSERT INTO {tmp} ({newNames}) SELECT {oldNames} FROM {tableName}"
    db.exec s!"DROP TABLE {tableName}"
    db.exec s!"ALTER TABLE {tmp} RENAME TO {tableName}"

instance : DBMonadWithMigrations M where
  currentDatabase := do
    -- The SQLite analogue of `information_schema.columns`.
    let rows ← query <|
      "SELECT m.name AS tbl, p.name AS col, p.type AS ty, p.[notnull] AS nn " ++
      "FROM sqlite_master m JOIN pragma_table_info(m.name) p " ++
      "WHERE m.type = 'table' AND m.name NOT LIKE 'sqlite_%' " ++
      "ORDER BY m.name, p.cid"
    let mut tables : Std.HashMap String TableRecipe := ∅
    for row in rows do
      if let (some tbl, some col, some ty) := (row.get? "tbl", row.get? "col", row.get? "ty") then
        if let some dbtype := parseDBType ty then
          -- `notnull` is `1` for a `NOT NULL` column, `0` otherwise.
          let nullable := row.getD "nn" "0" == "0"
          let column : Column := { type := dbtype, nullable := nullable }
          let existing := (tables.getD tbl { columns := ∅ }).columns
          tables := tables.insert tbl { columns := existing.insert col column }
    return { tables := tables }
  execute op := do
    let db ← read
    match SQL.Migration.Operation.fromDatabaseOperation op with
    | .createTable cmd => db.exec cmd.toString
    | .dropTable cmd => db.exec cmd.toString
    | .renameTable cmd => db.exec cmd.toString
    | .alterTable cmd =>
      -- SQLite cannot change a column's type or nullability in place. If any command does so, rebuild
      -- the table (which also applies any add/drop/rename in the same operation). Otherwise SQLite
      -- supports the changes directly, one statement per command.
      if cmd.commands.any fun c => match c with | .alterColumn .. => true | _ => false then
        rebuildTable cmd.tableName cmd.commands
      else
        for command in cmd.commands do
          db.exec s!"ALTER TABLE {cmd.tableName} {command.toString}"

end Sqlite
