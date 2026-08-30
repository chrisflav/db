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

This module provides a database backend backed by
[`leansqlite`](https://github.com/leanprover/leansqlite), the official Lean bindings for SQLite.
It mirrors the PostgreSQL backend: the typed queries are turned into SQL strings by
`Db.Backends.Sql` and executed through the SQLite C bindings.

The backend runs in the `Sqlite.M` monad, a thin reader over an open `SQLite` connection. Because
SQLite is embedded (the amalgamation is bundled by `leansqlite`), no external database server is
required and databases can be in-memory (`":memory:"`) or file-backed.

Two things differ from PostgreSQL and are handled here:

* Schema introspection uses `sqlite_master` joined with `pragma_table_info`, rather than
  `information_schema.columns` (which SQLite does not have).
* `ALTER TABLE` in SQLite supports only one change per statement, cannot change a column's type or
  nullability at all, and cannot add a `NOT NULL` column. So `execute` emits one statement per
  command where SQLite supports it, and otherwise rebuilds the table (create a new table with the
  target schema, copy the data over, drop the old table, rename the new one into place, and
  re-create the indexes and triggers that `DROP TABLE` took with it) inside a transaction.
-/

namespace Sqlite

open scoped SQLite

/-- The SQLite backend monad: a reader over an open connection. Errors surface as `IO`
exceptions. -/
abbrev M := ReaderT SQLite IO

/-- Run a SQLite computation against the database at `path` (use `":memory:"` for an in-memory
database), opening the connection first. -/
def runDB (path : System.FilePath) {α : Type} (x : M α) : IO α := do
  let db ← SQLite.open path
  x.run db

/-- One row of a result: a map from (aliased) column name to its textual value, where `none` is
SQL's `NULL`. Keeping `NULL` apart from the empty string matters as soon as a column can hold
unbounded text, for which the empty string is an ordinary value. -/
abbrev Row := Std.HashMap String (Option String)

/-- The textual value of a column of a row, `none` if the column is absent or `NULL`. -/
def Row.text? (row : Row) (name : String) : Option String :=
  (row.get? name).join

/-- The textual value of a column of a row, or `fallback` if it is absent or `NULL`. -/
def Row.textD (row : Row) (name : String) (fallback : String) : String :=
  (row.text? name).getD fallback

/-- Run a `SELECT` statement and return the resulting rows. This matches the representation the
query interpretation expects: values are decoded from strings via `Column.ofRawValue?`, exactly as
in the PostgreSQL backend. -/
def query (sql : String) : M (Array Row) := do
  let db ← read
  let stmt ← db.prepare sql
  let ncols := stmt.columnCount.toNat
  let mut rows : Array Row := #[]
  while (← stmt.step) do
    let mut row : Row := ∅
    for i in [0:ncols] do
      let name ← stmt.columnName (Int32.ofNat i)
      let val ← if (← stmt.columnNull (Int32.ofNat i)) then
          pure none
        else
          some <$> stmt.columnText (Int32.ofNat i)
      row := row.insert name val
    rows := rows.push row
  return rows

instance (d : Database) : DBMonad d M where
  lookup {view} q := do
    let sql : SQL.Select := .fromQuery q
    let rows ← query sql.toString
    -- A row whose columns cannot all be decoded is an error rather than a row to skip: dropping it
    -- would answer the query with silently fewer rows than it matched.
    rows.mapM fun row => do
      let mut map := default
      for idx in Enum.all view.Index do
        let name := s!"{idx}"
        let some raw := row.get? name
          | throw (IO.userError s!"SQLite backend: the result has no column `{name}`.")
        let some val := (view.name idx).column.ofRawValue? raw
          | throw (IO.userError
              s!"SQLite backend: cannot read {repr raw} as a value of column `{name}`.")
        map := map.insert idx val
      let some value := Enum.fromHashMap? map
        | throw (IO.userError "SQLite backend: the result is missing a column.")
      return { value := value }
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
  else if low == "text" then
    some .text
  else if low.startsWith "varchar" || low.startsWith "character varying" then
    match low.splitOn "(" with
    | [_, rest] =>
      match rest.splitOn ")" with
      | n :: _ => some (.varchar (n.toNat?.getD 0))
      | _ => some (.varchar 0)
    -- A `varchar` with no length is unbounded in SQLite, which is what `text` means here.
    | _ => some .text
  else
    none

/-- A column as tracked while rebuilding a table. -/
structure RebuildColumn where
  name : String
  /-- The declared type, as SQLite reports and accepts it. -/
  type : String
  notNull : Bool
  /-- The column's 1-based position in the table's `PRIMARY KEY`, or `0` if it is not part of it. -/
  primaryKey : Nat
  /-- The column's `DEFAULT`, if it has one. Held parsed rather than as the text
  `pragma_table_info` reports, which has already had the parentheses of an expression stripped and
  would not parse back as SQL. -/
  default? : Option ColumnDefault
  /-- The column's name in the *existing* table, whose data is copied across the rebuild, or `none`
  for a freshly added column, which has no data to preserve. -/
  source : Option String

/-- Introspect the current columns of `tableName`, in definition order, as `RebuildColumn`s whose
`source` is their own name (they all exist and their data must be preserved). -/
def currentColumns (tableName : String) : M (Array RebuildColumn) := do
  let rows ← query <|
    s!"SELECT name AS nm, type AS ty, [notnull] AS nn, pk, dflt_value AS dv " ++
    s!"FROM pragma_table_info('{tableName}') ORDER BY cid"
  return rows.filterMap fun row =>
    match row.text? "nm", row.text? "ty" with
    | some n, some ty =>
      -- A default on a column whose type has no `DBType` counterpart is still carried across the
      -- rebuild, as an expression.
      letI default? := (row.text? "dv").map fun d =>
        ((parseDBType ty).bind fun t => SQL.ColumnDefault.parse? t d).getD (.call d)
      some { name := n, type := ty, notNull := row.textD "nn" "0" == "1"
             primaryKey := (row.textD "pk" "0").toNat?.getD 0, default? := default?
             source := some n }
    | _, _ => none

/-- The `CREATE INDEX`/`CREATE TRIGGER` statements of every index and trigger attached to
`tableName`. `DROP TABLE` destroys these, so a rebuild has to re-run them afterwards. Indexes SQLite
creates itself for a `PRIMARY KEY` or `UNIQUE` constraint have no statement of their own and are not
listed here; see `unrecoverableConstraints`. -/
def auxiliaryObjects (tableName : String) : M (Array String) := do
  let rows ← query <|
    s!"SELECT sql FROM sqlite_master WHERE tbl_name = '{tableName}' " ++
    "AND type IN ('index', 'trigger') AND sql IS NOT NULL"
  return rows.filterMap (·.text? "sql")

/-- The names of `UNIQUE` constraints of `tableName` that a rebuild cannot reproduce. A `UNIQUE`
constraint written inside `CREATE TABLE` is backed by an index SQLite generated itself, so it has no
statement to re-run and is not visible in `pragma_table_info` either; rebuilding the table would
drop it silently. A `PRIMARY KEY` is exempt: `currentColumns` recovers it from `pragma_table_info`.
-/
def unrecoverableConstraints (tableName : String) : M (Array String) := do
  let rows ← query <|
    s!"SELECT il.name AS nm FROM pragma_index_list('{tableName}') il " ++
    "LEFT JOIN sqlite_master m ON m.name = il.name AND m.type = 'index' " ++
    "WHERE il.origin = 'u' AND m.sql IS NULL"
  return rows.filterMap (·.text? "nm")

open SQL.Migration in
/-- Apply one `ALTER TABLE` command to the working column list of a table rebuild. -/
def applyAlterCommand (cols : Array RebuildColumn) : AlterTableCommand → Array RebuildColumn
  | .addColumn field =>
    cols.push { name := field.name, type := field.type, notNull := !field.nullable
                primaryKey := 0, default? := field.default?, source := none }
  | .dropColumn name => cols.filter fun c => c.name != name
  | .renameColumn old new => cols.map fun c => if c.name == old then { c with name := new } else c
  | .alterColumn name (.setType ty) =>
    cols.map fun c => if c.name == name then { c with type := ty } else c
  | .alterColumn name (.setNullable nullable) =>
    cols.map fun c => if c.name == name then { c with notNull := !nullable } else c
  | .alterColumn name (.setDefault dflt) =>
    cols.map fun c => if c.name == name then { c with default? := dflt } else c

open SQL.Migration in
/-- Rebuild `tableName` to the schema obtained by applying `commands` to its current columns. SQLite
supports neither `ALTER COLUMN` nor adding a `NOT NULL` column, so those changes are realised by the
standard create/copy/drop/rename dance, run inside a transaction so it is all-or-nothing.

`DROP TABLE` also drops the table's indexes and triggers, so they are captured beforehand and
re-created afterwards, and the `PRIMARY KEY` is carried over from `pragma_table_info`. A `UNIQUE`
constraint written inside the original `CREATE TABLE` cannot be recovered this way, so rather than
dropping it silently the rebuild refuses to run. -/
def rebuildTable (tableName : String) (commands : List AlterTableCommand) : M Unit := do
  let db ← read
  let unrecoverable ← unrecoverableConstraints tableName
  unless unrecoverable.isEmpty do
    throw <| IO.userError <|
      s!"SQLite backend: cannot rebuild table `{tableName}`, as it has UNIQUE constraint(s) " ++
      s!"({", ".intercalate unrecoverable.toList}) declared in its `CREATE TABLE` statement, " ++
      "which the rebuild would silently drop. Migrate this table by hand."
  let current ← currentColumns tableName
  let aux ← auxiliaryObjects tableName
  let newCols := commands.foldl applyAlterCommand current
  let fieldDefs := newCols.toList.map fun c =>
    letI dflt := match c.default? with
      | some d => s!" DEFAULT {SQL.ColumnDefault.toString d}"
      | none => ""
    s!"{c.name} {c.type}{if c.notNull then " NOT NULL" else ""}{dflt}"
  let pkCols := (newCols.toList.filter (·.primaryKey > 0)).mergeSort
    (fun c₁ c₂ => c₁.primaryKey ≤ c₂.primaryKey) |>.map (·.name)
  let constraints := if pkCols.isEmpty then [] else [s!"PRIMARY KEY ({", ".intercalate pkCols})"]
  -- Columns present both before and after keep their data; match old name → new name.
  let copyPairs := newCols.toList.filterMap fun c => c.source.map (·, c.name)
  let newNames := ", ".intercalate (copyPairs.map (·.2))
  let oldNames := ", ".intercalate (copyPairs.map (·.1))
  let tmp := s!"__db_migrate_{tableName}"
  db.transaction do
    db.exec s!"CREATE TABLE {tmp} (\n  {",\n  ".intercalate (fieldDefs ++ constraints)}\n)"
    unless copyPairs.isEmpty do
      db.exec s!"INSERT INTO {tmp} ({newNames}) SELECT {oldNames} FROM {tableName}"
    db.exec s!"DROP TABLE {tableName}"
    db.exec s!"ALTER TABLE {tmp} RENAME TO {tableName}"
    for sql in aux do
      db.exec sql

instance : DBMonadWithMigrations M where
  currentDatabase := do
    -- The SQLite analogue of `information_schema.columns`.
    let rows ← query <|
      "SELECT m.name AS tbl, p.name AS col, p.type AS ty, p.[notnull] AS nn, " ++
      "p.dflt_value AS dv " ++
      "FROM sqlite_master m JOIN pragma_table_info(m.name) p " ++
      "WHERE m.type = 'table' AND m.name NOT LIKE 'sqlite_%' " ++
      "ORDER BY m.name, p.cid"
    let mut tables : Std.HashMap String TableRecipe := ∅
    for row in rows do
      if let (some tbl, some col, some ty) :=
          (row.text? "tbl", row.text? "col", row.text? "ty") then
        -- Skipping a column we cannot represent would make the reported schema disagree with the
        -- database, and the migration derived from it would then fail against the real table.
        let some dbtype := parseDBType ty
          | throw <| IO.userError <|
              s!"SQLite backend: column `{col}` of table `{tbl}` has type `{ty}`, which has no " ++
              "`DBType` counterpart, so the current schema cannot be represented."
        -- `notnull` is `1` for a `NOT NULL` column, `0` otherwise.
        let nullable := row.textD "nn" "0" == "0"
        let default? := (row.text? "dv").bind (SQL.ColumnDefault.parse? dbtype)
        let column : Column := { type := dbtype, nullable := nullable, default? := default? }
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
      -- SQLite cannot change a column's type or nullability in place, and rejects `ADD COLUMN`
      -- with `NOT NULL` (it would have to fill the existing rows with `NULL`). If any command does
      -- one of those, rebuild the table, which also applies the remaining commands of the same
      -- operation. Otherwise SQLite supports the changes directly, one statement per command.
      -- SQLite rejects `ADD COLUMN` with a non-constant default whatever the column's
      -- nullability, and a `NOT NULL` column whose default is missing or `NULL`; the rest of an
      -- `ADD COLUMN` it accepts.
      let needsRebuild := cmd.commands.any fun c =>
        match c with
        | .alterColumn .. => true
        | .addColumn field =>
          match field.default? with
          | some (.call _) => true
          | some .null => !field.nullable
          | some _ => false
          | none => !field.nullable
        | _ => false
      if needsRebuild then
        rebuildTable cmd.tableName cmd.commands
      else
        for command in cmd.commands do
          db.exec s!"ALTER TABLE {cmd.tableName} {command.toString}"

end Sqlite
