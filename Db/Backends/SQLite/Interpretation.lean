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

/-- Decode the rows of a result into the entries of `view`.

A row whose columns cannot all be decoded is an error rather than a row to skip: dropping it would
answer the query with silently fewer rows than it matched. -/
def decodeRows {d : Database} (view : View d) (rows : Array Row) : M (Array view.Entry) :=
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

instance (d : Database) : DBMonad d M where
  lookup {view} q := do
    let sql : SQL.Select := .fromQuery q
    decodeRows view (← query sql.toString)
  insert {table} data := do
    let db ← read
    let sql : SQL.Insert := .fromInsert data
    db.exec sql.toString
  insertReturning {table} data := do
    let sql : SQL.Insert := { SQL.Insert.fromInsert data with returning := true }
    decodeRows (Table.view table) (← query sql.toString)
  update {table} upd := do
    let db ← read
    let sql : SQL.Update := .fromUpdate upd
    -- An `UPDATE` with no assignment is not a statement; it also changes nothing.
    if sql.assignments.isEmpty then
      return 0
    db.exec sql.toString
    -- `changes` reports the number of rows affected by the last statement.
    return (← db.changes).toInt.toNat
  updateReturning {table} upd := do
    let sql : SQL.Update := { SQL.Update.fromUpdate upd with returning := true }
    if sql.assignments.isEmpty then
      return #[]
    decodeRows (Table.view table) (← query sql.toString)
  delete {table} del := do
    let db ← read
    let sql : SQL.Delete := .fromDelete del
    db.exec sql.toString
    return (← db.changes).toInt.toNat
  deleteReturning {table} del := do
    let sql : SQL.Delete := { SQL.Delete.fromDelete del with returning := true }
    decodeRows (Table.view table) (← query sql.toString)

instance : DBMonadTransactional M where
  -- `SQLite.transaction` commits when the action returns and rolls back when it throws.
  withTransaction x := fun db => db.transaction (x.run db)

/-- Whether `needle` occurs in `haystack` as a whole word, i.e. not as part of a longer
identifier. Both are compared as given, so the caller upper-cases them. -/
def containsWord (haystack needle : String) : Bool := Id.run do
  let isIdent (c : Char) : Bool := c.isAlphanum || c == '_'
  let hs := haystack.toList
  let ns := needle.toList
  if ns.isEmpty || hs.length < ns.length then
    return false
  for i in [0:hs.length - ns.length + 1] do
    let found := (List.range ns.length).all fun j => hs[i + j]! == ns[j]!
    let beforeOk := i == 0 || !isIdent hs[i - 1]!
    let afterOk := i + ns.length == hs.length || !isIdent hs[i + ns.length]!
    if found && beforeOk && afterOk then
      return true
  return false

/-- Whether `tableName` was declared `AUTOINCREMENT`. SQLite records this nowhere but in the text
of the `CREATE TABLE`, so it is read back from there; the word is matched as a whole one, so that a
table or column whose name merely contains it is not mistaken for a generated key. -/
def isAutoIncrement (tableName : String) : M Bool := do
  let rows ← query <|
    s!"SELECT sql FROM sqlite_master WHERE type = 'table' AND name = '{tableName}'"
  letI declaration := (rows[0]?.bind (·.text? "sql")).getD ""
  return containsWord declaration.toUpper "AUTOINCREMENT"

/-- Parse the referential action SQLite reports for a foreign key. -/
def parseForeignKeyAction (s : String) : ForeignKeyAction :=
  match s.toUpper with
  | "RESTRICT" => .restrict
  | "CASCADE" => .cascade
  | "SET NULL" => .setNull
  | "SET DEFAULT" => .setDefault
  | _ => .noAction

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
  /-- Whether the database assigns the column's value. -/
  autoIncrement : Bool
  /-- The column's name in the *existing* table, whose data is copied across the rebuild, or `none`
  for a freshly added column, which has no data to preserve. -/
  source : Option String

/-- Introspect the current columns of `tableName`, in definition order, as `RebuildColumn`s whose
`source` is their own name (they all exist and their data must be preserved). -/
def currentColumns (tableName : String) : M (Array RebuildColumn) := do
  let autoIncrement ← isAutoIncrement tableName
  let rows ← query <|
    s!"SELECT name AS nm, type AS ty, [notnull] AS nn, pk, dflt_value AS dv " ++
    s!"FROM pragma_table_info('{tableName}') ORDER BY cid"
  let keySize := rows.filter (fun row => (row.textD "pk" "0").toNat?.getD 0 > 0) |>.size
  return rows.filterMap fun row =>
    match row.text? "nm", row.text? "ty" with
    | some n, some ty =>
      -- A default on a column whose type has no `DBType` counterpart is still carried across the
      -- rebuild, as an expression.
      letI default? := (row.text? "dv").map fun d =>
        ((parseDBType ty).bind fun t => SQL.ColumnDefault.parse? t d).getD (.call d)
      letI position := (row.textD "pk" "0").toNat?.getD 0
      some { name := n, type := ty, notNull := row.textD "nn" "0" == "1"
             primaryKey := position, default? := default?
             autoIncrement :=
               autoIncrement && position == 1 && keySize == 1 && parseDBType ty == some .int
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

/-- The column groups of the `UNIQUE` constraints `tableName` declares inside its `CREATE TABLE`.

Those are backed by an index SQLite generated itself, so unlike a `CREATE UNIQUE INDEX` they have
no statement of their own for `auxiliaryObjects` to re-run, and a rebuild has to declare them
again. -/
def inlineUnique (tableName : String) : M (List (List String)) := do
  let indexRows ← query <|
    s!"SELECT il.name AS nm FROM pragma_index_list('{tableName}') il " ++
    "LEFT JOIN sqlite_master m ON m.name = il.name AND m.type = 'index' " ++
    "WHERE il.origin = 'u' AND m.sql IS NULL ORDER BY il.name"
  let mut res : List (List String) := []
  for indexRow in indexRows do
    let some indexName := indexRow.text? "nm" | continue
    let columnRows ← query <|
      s!"SELECT name AS nm FROM pragma_index_info('{indexName}') ORDER BY seqno"
    res := (columnRows.toList.filterMap (·.text? "nm")) :: res
  return res.reverse

open SQL.Migration in
/-- Apply one `ALTER TABLE` command to the working column list of a table rebuild. -/
def applyAlterCommand (cols : Array RebuildColumn) : AlterTableCommand → Array RebuildColumn
  | .addColumn field =>
    cols.push { name := field.name, type := field.type, notNull := !field.nullable
                primaryKey := 0, default? := field.default?, autoIncrement := field.autoIncrement
                source := none }
  | .dropColumn name => cols.filter fun c => c.name != name
  | .renameColumn old new => cols.map fun c => if c.name == old then { c with name := new } else c
  | .alterColumn name (.setType ty) =>
    cols.map fun c => if c.name == name then { c with type := ty } else c
  | .alterColumn name (.setNullable nullable) =>
    cols.map fun c => if c.name == name then { c with notNull := !nullable } else c
  | .alterColumn name (.setDefault dflt) =>
    cols.map fun c => if c.name == name then { c with default? := dflt } else c

/-- The columns, primary key and auto-increment flag of `tableName`, as `pragma_table_info` and the
`CREATE TABLE` text report them. -/
def tableColumns (tableName : String) : M (Std.HashMap String Column × List String) := do
  let autoIncrement ← isAutoIncrement tableName
  let rows ← query <|
    s!"SELECT name AS nm, type AS ty, [notnull] AS nn, pk, dflt_value AS dv " ++
    s!"FROM pragma_table_info('{tableName}') ORDER BY cid"
  -- Whether the primary key is a single column decides whether it is the table's rowid.
  let keySize := rows.filter (fun row => (row.textD "pk" "0").toNat?.getD 0 > 0) |>.size
  let mut columns : Std.HashMap String Column := ∅
  let mut key : Array (Nat × String) := #[]
  for row in rows do
    let (some col, some ty) := (row.text? "nm", row.text? "ty") | continue
    -- Skipping a column we cannot represent would make the reported schema disagree with the
    -- database, and the migration derived from it would then fail against the real table.
    let some dbtype := parseDBType ty
      | throw <| IO.userError <|
          s!"SQLite backend: column `{col}` of table `{tableName}` has type `{ty}`, which has " ++
          "no `DBType` counterpart, so the current schema cannot be represented."
    let position := (row.textD "pk" "0").toNat?.getD 0
    if position > 0 then
      key := key.push (position, col)
    -- A single-column `INTEGER PRIMARY KEY` is the table's rowid, which cannot be null and which
    -- SQLite nonetheless reports as nullable. Every other primary key column can be null, an old
    -- quirk SQLite keeps for compatibility, so its `notnull` is taken at face value.
    let isRowid := position == 1 && keySize == 1 && dbtype == .int
    let nullable := row.textD "nn" "0" == "0" && !isRowid
    let default? := (row.text? "dv").bind (SQL.ColumnDefault.parse? dbtype)
    columns := columns.insert col
      { type := dbtype, nullable := nullable, default? := default?
        autoIncrement := autoIncrement && isRowid }
  let sortedKey := (key.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))).map (·.2)
  return (columns, sortedKey)

/-- The groups of columns of `tableName` that a `UNIQUE` constraint holds together. The index
SQLite creates for the primary key has origin `pk` rather than `u` and is not one of them. -/
def tableUnique (tableName : String) : M (List (List String)) := do
  let indexRows ← query <|
    s!"SELECT name AS nm FROM pragma_index_list('{tableName}') WHERE origin = 'u' ORDER BY name"
  let mut res : List (List String) := []
  for indexRow in indexRows do
    let some indexName := indexRow.text? "nm" | continue
    let columnRows ← query <|
      s!"SELECT name AS nm FROM pragma_index_info('{indexName}') ORDER BY seqno"
    res := (columnRows.toList.filterMap (·.text? "nm")) :: res
  return res.reverse

/-- The foreign keys of `tableName`. `pragma_foreign_key_list` reports one row per referencing
column, which the `id` column groups into keys and `seq` orders within a key. -/
def tableForeignKeys (tableName : String) : M (List (ForeignKey String)) := do
  let rows ← query <|
    s!"SELECT id, seq, [table] AS ftbl, [from] AS col, [to] AS fcol, on_delete AS od, " ++
    s!"on_update AS ou FROM pragma_foreign_key_list('{tableName}') ORDER BY id, seq"
  let mut byId : Std.HashMap String (ForeignKey String) := ∅
  let mut order : Array String := #[]
  for row in rows do
    let (some id, some ftbl, some col) := (row.text? "id", row.text? "ftbl", row.text? "col")
      | continue
    -- A `to` of `NULL` means the key references the target's primary key implicitly; the column it
    -- names is the one at the same position in that key.
    let fcol ← match row.text? "fcol" with
      | some c => pure c
      | none => do
        let (_, targetKey) ← tableColumns ftbl
        let position := (row.textD "seq" "0").toNat?.getD 0
        pure (targetKey[position]?.getD col)
    match byId[id]? with
    | some fk =>
      byId := byId.insert id
        { fk with columns := fk.columns ++ [col], foreignColumns := fk.foreignColumns ++ [fcol] }
    | none =>
      order := order.push id
      byId := byId.insert id
        { columns := [col], foreignTable := ftbl, foreignColumns := [fcol]
          onDelete := parseForeignKeyAction (row.textD "od" "")
          onUpdate := parseForeignKeyAction (row.textD "ou" "") }
  return order.toList.filterMap (byId[·]?)

open SQL.Migration in
/-- Rebuild `tableName` to the schema obtained by applying `commands` to its current columns. SQLite
supports neither `ALTER COLUMN` nor adding a `NOT NULL` column, so those changes are realised by the
standard create/copy/drop/rename dance, run inside a transaction so it is all-or-nothing.

`DROP TABLE` also drops the table's indexes and triggers, so they are captured beforehand and
re-created afterwards, and the `PRIMARY KEY`, the generated key, the `UNIQUE` groups and the
foreign keys are carried over from the pragmas. A constraint naming a column the rebuild renames or
drops cannot be carried over, so rather than dropping it silently the rebuild refuses to run. -/
def rebuildTable (tableName : String) (commands : List AlterTableCommand) : M Unit := do
  let db ← read
  let current ← currentColumns tableName
  let aux ← auxiliaryObjects tableName
  let unique ← inlineUnique tableName
  let foreignKeys ← tableForeignKeys tableName
  let newCols := commands.foldl applyAlterCommand current
  let pkCols := (newCols.toList.filter (·.primaryKey > 0)).mergeSort
    (fun c₁ c₂ => c₁.primaryKey ≤ c₂.primaryKey) |>.map (·.name)
  -- A generated key is declared on the column and cannot be declared again below.
  let inlineKey : Option String :=
    match newCols.toList.filter (·.autoIncrement) with
    | [c] => if pkCols == [c.name] then some c.name else none
    | _ => none
  let fieldDefs := newCols.toList.map fun c =>
    if inlineKey == some c.name then
      s!"{c.name} INTEGER PRIMARY KEY AUTOINCREMENT"
    else
      letI dflt := match c.default? with
        | some d => s!" DEFAULT {SQL.ColumnDefault.toString d}"
        | none => ""
      s!"{c.name} {c.type}{if c.notNull then " NOT NULL" else ""}{dflt}"
  -- A column the rebuild kept under the same name is still the one a foreign key refers to.
  let kept : Std.HashSet String := .ofList (newCols.toList.filterMap fun c =>
    if c.source == some c.name then some c.name else none)
  for columns in unique ++ foreignKeys.map (·.columns) do
    unless columns.all kept.contains do
      throw <| IO.userError <|
        s!"SQLite backend: cannot rebuild table `{tableName}`, as its constraint on " ++
        s!"({", ".intercalate columns}) names columns the migration renames or drops, so the " ++
        "rebuild would silently drop the constraint. Migrate this table by hand."
  let uniqueDefs := unique.map fun columns => s!"UNIQUE ({", ".intercalate columns})"
  let foreignKeyDefs := foreignKeys.map fun fk =>
    s!"FOREIGN KEY ({", ".intercalate fk.columns}) " ++
      s!"REFERENCES {fk.foreignTable} ({", ".intercalate fk.foreignColumns}) " ++
      s!"ON DELETE {fk.onDelete.sql} ON UPDATE {fk.onUpdate.sql}"
  let constraints :=
    (if pkCols.isEmpty || inlineKey.isSome then []
      else [s!"PRIMARY KEY ({", ".intercalate pkCols})"]) ++ uniqueDefs ++ foreignKeyDefs
  -- Columns present both before and after keep their data; match old name → new name.
  let copyPairs := newCols.toList.filterMap fun c => c.source.map (·, c.name)
  let newNames := ", ".intercalate (copyPairs.map (·.2))
  let oldNames := ", ".intercalate (copyPairs.map (·.1))
  let tmp := s!"__db_migrate_{tableName}"
  -- Foreign key enforcement has to be off across the rebuild: another table referencing this one
  -- would otherwise block the `DROP TABLE`, and its references would be rewritten to point at the
  -- temporary table by the rename. The pragma is a no-op inside a transaction, so it is set around
  -- it, and what it was is restored afterwards.
  let pragmaRows ← query "PRAGMA foreign_keys"
  let enforcing := (pragmaRows[0]?.bind (·.text? "foreign_keys")).getD "0" == "1"
  if enforcing then
    db.exec "PRAGMA foreign_keys = OFF"
  try
    db.transaction do
      db.exec s!"CREATE TABLE {tmp} (\n  {",\n  ".intercalate (fieldDefs ++ constraints)}\n)"
      unless copyPairs.isEmpty do
        db.exec s!"INSERT INTO {tmp} ({newNames}) SELECT {oldNames} FROM {tableName}"
      db.exec s!"DROP TABLE {tableName}"
      db.exec s!"ALTER TABLE {tmp} RENAME TO {tableName}"
      for sql in aux do
        db.exec sql
    if enforcing then
      -- What the pragma would have caught while it was off.
      let violations ← query "PRAGMA foreign_key_check"
      unless violations.isEmpty do
        throw <| IO.userError <|
          s!"SQLite backend: rebuilding table `{tableName}` left {violations.size} row(s) " ++
          "violating a foreign key."
  finally
    if enforcing then
      db.exec "PRAGMA foreign_keys = ON"

instance : DBMonadWithMigrations M where
  abort message := throw <| IO.userError s!"SQLite backend: {message}"
  currentDatabase := do
    let tableRows ← query <|
      "SELECT name AS nm FROM sqlite_master " ++
      "WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
    let mut tables : Std.HashMap String TableRecipe := ∅
    for tableRow in tableRows do
      let some name := tableRow.text? "nm" | continue
      let (columns, primaryKey) ← tableColumns name
      tables := tables.insert name
        { columns := columns
          primaryKey := primaryKey
          unique := ← tableUnique name
          foreignKeys := ← tableForeignKeys name }
    return { tables := tables }
  execute op := do
    let db ← read
    match SQL.Migration.Operation.fromDatabaseOperation op with
    | .createTable cmd =>
      -- Rejected here rather than rendered into a table with a key nobody declared.
      if let some reason := cmd.sqliteError? then
        throw <| IO.userError s!"SQLite backend: {reason}"
      db.exec (cmd.toString .sqlite)
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
          db.exec s!"ALTER TABLE {cmd.tableName} {command.toString .sqlite}"

end Sqlite
