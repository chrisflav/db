/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Backends.PostgreSQL.Basic
import Db.Utils.FromString
import Db.Backends.Sql
import Db.Interpretation.Basic
import Db.Model

def Database.resolveName (d : Database) (tableName columnName : String) : Option d.Name :=
  match (FromString.fromString tableName : Option d.Index) with
  | some tableName =>
    match (FromString.fromString columnName : Option (d.tables tableName).Index) with
    | some columnName => some (.ident { tableName := tableName, columnName := columnName })
    | none => none
  | none => none

namespace PostgreSQL

inductive Exception where
  | connectionError
  | fatal
  /-- A value the database returned could not be read as the type the view declares for it. -/
  | decodeError (message : String)
  /-- A migration that cannot be carried out. -/
  | migrationError (message : String)
  /-- A failure reported by a layer above the backend. -/
  | userError (message : String)
  deriving Repr

structure State where
  /-- The connection info for the connection. Needed to reconnect. -/
  connectionInfo : String
  connection : Connection

abbrev M := ExceptT Exception (StateT State IO)

nonrec def M.run (s : State) {α : Type} (x : M α) : IO (Except Exception α) := do
  return (← x.run.run s).1

def runDB (connectionInfo : String) {α : Type} (x : M α) : IO (Except Exception α) := do
  let conn ← connect connectionInfo
  match conn with
  | some conn => x.run { connectionInfo := connectionInfo, connection := conn }
  | none => return .error .connectionError

/-- Decode the rows of a result into the entries of `view`.

A row whose columns cannot all be decoded is an error rather than a row to skip: dropping it would
answer the query with silently fewer rows than it matched. -/
def decodeRows {d : Database} (view : View d) (rows : Array (Std.HashMap String (Option String))) :
    M (Array view.Entry) :=
  rows.mapM fun row ↦ do
    let mut map := default
    for idx in Enum.all view.Index do
      let name := s!"{idx}"
      let some raw := row.get? name
        | throw (.decodeError s!"the result has no column `{name}`.")
      let some val := (view.name idx).column.ofRawValue? raw
        | throw (.decodeError s!"cannot read {repr raw} as a value of column `{name}`.")
      map := map.insert idx val
    let some value := Enum.fromHashMap? map
      | throw (.decodeError "the result is missing a column.")
    return { value := value }

/-- Run a statement expected to return rows, and return them. -/
def rowsOf (sql : String) : M (Array (Std.HashMap String (Option String))) := do
  let conn := (← get).connection
  match ← conn.exec sql with
  | .data data => return data.optRows
  | .success _ => return #[]
  | .failure e =>
    IO.println s!"{repr e}"
    throw .fatal

/-- Run a statement that changes rows, and return how many it changed, as libpq's command tag
reports it. -/
def execCounting (sql : String) : M Nat := do
  let conn := (← get).connection
  match ← conn.exec sql with
  | .data data => return data.nrows
  | .success affected => return affected
  | .failure e =>
    IO.println s!"{repr e}"
    throw .fatal

instance (d : Database) : DBMonad d M where
  lookup {view} q := do
    let sql : SQL.Select := .fromQuery q
    decodeRows view (← rowsOf sql.toString)
  insert {table} data := do
    let sql : SQL.Insert := .fromInsert data
    _ ← execCounting sql.toString
  insertReturning {table} data := do
    let sql : SQL.Insert := { SQL.Insert.fromInsert data with returning := SQL.columnNames table }
    decodeRows (Table.view table) (← rowsOf sql.toString)
  update {table} upd := do
    let sql : SQL.Update := .fromUpdate upd
    -- An `UPDATE` with no assignment is not a statement; it also changes nothing.
    if sql.assignments.isEmpty then
      return 0
    execCounting sql.toString
  updateReturning {table} upd := do
    let sql : SQL.Update := { SQL.Update.fromUpdate upd with returning := SQL.columnNames table }
    if sql.assignments.isEmpty then
      return #[]
    decodeRows (Table.view table) (← rowsOf sql.toString)
  delete {table} del := do
    let sql : SQL.Delete := .fromDelete del
    execCounting sql.toString
  deleteReturning {table} del := do
    let sql : SQL.Delete := { SQL.Delete.fromDelete del with returning := SQL.columnNames table }
    decodeRows (Table.view table) (← rowsOf sql.toString)

/-- Run a statement, ignoring its result. -/
def execIgnoring (sql : String) : M Unit := do
  let conn := (← get).connection
  _ ← conn.exec sql

/-- The name a nested transaction saves the connection under. Duplicates are fine: `ROLLBACK TO`
and `RELEASE` act on the most recent savepoint of the name, which is the innermost one. -/
def savepointName : String := "db_savepoint"

instance : DBMonadTransactional M where
  withTransaction x := do
    -- Nested inside a transaction already in progress, this is a savepoint: a second `BEGIN` is a
    -- no-op PostgreSQL only warns about, so the inner `COMMIT` would commit the outer transaction.
    let nested := (← get).connection.transactionStatus != .idle
    execIgnoring (if nested then s!"SAVEPOINT {savepointName}" else "BEGIN")
    try
      let a ← x
      if nested then
        execIgnoring s!"RELEASE SAVEPOINT {savepointName}"
      else if (← get).connection.transactionStatus == .inError then
        -- A `COMMIT` of a transaction the server has aborted silently rolls back and reports
        -- success, so reporting one here would claim the work was kept when it was discarded.
        execIgnoring "ROLLBACK"
        throw <| .userError <|
          "the transaction was aborted by a statement the database rejected, so it was rolled " ++
          "back rather than committed"
      else
        execIgnoring "COMMIT"
      return a
    catch e =>
      -- Only an `Exception` of this monad is caught here; an `IO` error thrown underneath escapes
      -- with the transaction still open, and the connection has to be discarded.
      if nested then
        execIgnoring s!"ROLLBACK TO SAVEPOINT {savepointName}"
        execIgnoring s!"RELEASE SAVEPOINT {savepointName}"
      else
        execIgnoring "ROLLBACK"
      throw e

structure InformationSchema where
  table_name : VarChar 100
  column_name : VarChar 100
  is_nullable : Bool
  /-- Whether PostgreSQL generates this column's value, i.e. it was declared `AS IDENTITY`. -/
  is_identity : Bool
  data_type : VarChar 100
  -- TODO: add `DBType.nat` and change this to `Nat`
  character_maximum_length : Option Int
  /-- The SQL text of the column's `DEFAULT`, with the explicit cast PostgreSQL appends to it. -/
  column_default : Option String
  table_schema : VarChar 100
  deriving Repr

def InformationSchema.column (info : InformationSchema) : Option Column := do
  let dbtype : DBType ← do
    match info.data_type.val with
    | "integer" => pure DBType.int
    | "boolean" => pure DBType.bool
    | "text" => pure DBType.text
    | "character varying" =>
      match info.character_maximum_length with
      | some n => pure <| DBType.varchar n.toNat
      -- A `character varying` with no declared length is unbounded, which is what `text` means.
      | none => pure DBType.text
    | _ => none
  pure
    { type := dbtype
      nullable := info.is_nullable
      -- The sequence an identity column draws from is not a default anyone declares.
      default? :=
        if info.is_identity then none
        else info.column_default.bind fun d =>
          SQL.ColumnDefault.parse? dbtype (SQL.stripCast d)
      autoIncrement := info.is_identity }

generate_table PostgreSQL.InformationSchema

inductive CatalogIndex : Type
  | information_schema
  deriving Hashable, DecidableEq, Repr, Enum

instance : ToString CatalogIndex where
  toString
    | .information_schema => "information_schema.columns"

instance : FromString CatalogIndex where
  fromString
    | "information_schema.columns" => some .information_schema
    | _ => none

instance : Indexing CatalogIndex where

abbrev catalog : Database where
  Index := CatalogIndex
  tables
    | .information_schema => InformationSchemaTable

def InformationSchema.model : Model catalog InformationSchema where
  index := .information_schema

/-- Run a statement and return its rows, in which `none` is SQL's `NULL`. Used for the catalogue
queries, which have no `DBType` counterpart for every column they return. -/
def query (sql : String) : M (Array (Std.HashMap String (Option String))) := do
  let conn := (← get).connection
  match ← conn.exec sql with
  | .data data => return data.optRows
  | .success _ => return #[]
  | .failure err =>
    IO.println s!"Error {repr err}"
    throw .fatal

/-- Parse the single-letter referential action `pg_constraint` reports. -/
def parseForeignKeyAction (s : String) : ForeignKeyAction :=
  match s with
  | "r" => .restrict
  | "c" => .cascade
  | "n" => .setNull
  | "d" => .setDefault
  | _ => .noAction

/--
The primary key, unique groups and foreign keys of every table of the `public` schema.

Read from `pg_constraint` rather than `information_schema`: the standard views report the
referencing and the referenced columns of a foreign key in two separate rows sets that cannot be
paired reliably, whereas `conkey` and `confkey` are ordered arrays that can.
-/
def catalogConstraints :
    M (Std.HashMap String (List String × List (List String) × List (ForeignKey String))) := do
  let rows ← query <|
    "SELECT rel.relname AS tbl, c.contype AS kind, " ++
    "coalesce(frel.relname, '') AS ftbl, c.confdeltype AS del, c.confupdtype AS upd, " ++
    "(SELECT coalesce(string_agg(a.attname, ',' ORDER BY k.ord), '') " ++
    " FROM unnest(c.conkey) WITH ORDINALITY AS k(attnum, ord) " ++
    " JOIN pg_attribute a ON a.attrelid = c.conrelid AND a.attnum = k.attnum) AS cols, " ++
    "(SELECT coalesce(string_agg(a.attname, ',' ORDER BY k.ord), '') " ++
    " FROM unnest(coalesce(c.confkey, '{}')) WITH ORDINALITY AS k(attnum, ord) " ++
    " JOIN pg_attribute a ON a.attrelid = c.confrelid AND a.attnum = k.attnum) AS fcols " ++
    "FROM pg_constraint c " ++
    "JOIN pg_class rel ON rel.oid = c.conrelid " ++
    "LEFT JOIN pg_class frel ON frel.oid = c.confrelid " ++
    "JOIN pg_namespace n ON n.oid = rel.relnamespace " ++
    "WHERE n.nspname = 'public' AND c.contype IN ('p', 'u', 'f') " ++
    "ORDER BY rel.relname, c.conname"
  let mut res : Std.HashMap String (List String × List (List String) × List (ForeignKey String)) :=
    ∅
  for row in rows do
    let (some tbl, some kind, some cols) := (row.get? "tbl" >>= id, row.get? "kind" >>= id,
      row.get? "cols" >>= id) | continue
    let columns := (cols.splitOn ",").filter (· != "")
    let (primaryKey, unique, foreignKeys) := res.getD tbl ([], [], [])
    match kind with
    | "p" => res := res.insert tbl (columns, unique, foreignKeys)
    | "u" => res := res.insert tbl (primaryKey, unique ++ [columns], foreignKeys)
    | _ =>
      let foreignColumns := ((row.get? "fcols" >>= id).getD "").splitOn ","
      let fk : ForeignKey String :=
        { columns := columns
          foreignTable := ((row.get? "ftbl" >>= id).getD "")
          foreignColumns := foreignColumns.filter (· != "")
          onDelete := parseForeignKeyAction ((row.get? "del" >>= id).getD "a")
          onUpdate := parseForeignKeyAction ((row.get? "upd" >>= id).getD "a") }
      res := res.insert tbl (primaryKey, unique, foreignKeys ++ [fk])
  return res

/-- The indexes of every table in `public` that a `CREATE INDEX` created.

`indisprimary` and the indexes backing a `UNIQUE` constraint are excluded: those are the
constraints' own, reported by `catalogConstraints`, and dropping one would drop the constraint with
it. `pg_get_indexdef` gives the definition back in PostgreSQL's canonical spelling, which
`parseCreateIndex?` normalises — a `lower(title)` on a `varchar` column comes back as
`lower((title)::text)`. -/
def catalogIndexes : M (Std.HashMap String (List (TableIndex String))) := do
  let rows ← query <|
    "SELECT rel.relname AS tbl, cls.relname AS idx, pg_get_indexdef(i.indexrelid) AS ddl " ++
    "FROM pg_index i " ++
    "JOIN pg_class cls ON cls.oid = i.indexrelid " ++
    "JOIN pg_class rel ON rel.oid = i.indrelid " ++
    "JOIN pg_namespace n ON n.oid = rel.relnamespace " ++
    "WHERE n.nspname = 'public' AND NOT i.indisprimary " ++
    "AND NOT EXISTS (SELECT 1 FROM pg_constraint c WHERE c.conindid = i.indexrelid) " ++
    "ORDER BY rel.relname, cls.relname"
  let mut res : Std.HashMap String (List (TableIndex String)) := ∅
  for row in rows do
    let (some tbl, some idx, some ddl) :=
      (row.get? "tbl" >>= id, row.get? "idx" >>= id, row.get? "ddl" >>= id) | continue
    let some parsed := SQL.Migration.parseCreateIndex? idx ddl | continue
    res := res.insert tbl (res.getD tbl [] ++ [parsed])
  return res

instance : DBMonadWithMigrations M where
  abort message := do
    IO.println s!"PostgreSQL backend: {message}"
    throw <| .migrationError message
  execute operation := do
    let conn := (← get).connection
    let sql : SQL.Migration.Operation := .fromDatabaseOperation operation
    IO.println s!"Executing {sql.toString .postgres}"
    let res ← conn.exec (sql.toString .postgres)
    match res with
    | .failure err =>
      IO.println s!"Error {repr err}"
      throw .fatal
    | .data _ =>
      IO.println s!"Returned data when no data was expected."
      throw .fatal
    | .success _ => pure ()
  executeIndex op := do
    let conn := (← get).connection
    let sql := SQL.Migration.indexOperationToString op
    match ← conn.exec sql with
    | .failure err =>
      IO.println s!"Error {repr err}"
      throw .fatal
    | .data _ =>
      IO.println s!"Returned data when no data was expected."
      throw .fatal
    | .success _ => pure ()
  currentDatabase := do
    let q : InformationSchema.model.Query :=
      .filter
        (.eq (.var InformationSchemaIndex.table_schema (.varchar 100))
                     (.str (v"public")))
        (.all _)
    let infos ← q.fetch
    let constraints ← catalogConstraints
    let indexes ← catalogIndexes
    let mut tables : Std.HashMap String TableRecipe := .emptyWithCapacity
    for info in infos do
      if let some col := info.column then
      let name := info.table_name.val
      let (primaryKey, unique, foreignKeys) := constraints.getD name ([], [], [])
      let columns :=
        (tables.getD name { columns := ∅ }).columns.insert info.column_name.val col
      tables := tables.insert name
        { columns := columns
          primaryKey := primaryKey
          unique := unique
          foreignKeys := foreignKeys
          indexes := indexes.getD name [] }
    return { tables := tables }

end PostgreSQL
