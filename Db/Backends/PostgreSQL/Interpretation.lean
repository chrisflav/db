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

instance (d : Database) : DBMonad d M where
  lookup {view} q := do
    let conn := (← get).connection
    let sql : SQL.Select := .fromQuery q
    let res ← conn.exec sql.toString
    match res with
    | .data data =>
        data.optRows.filterMapM <| fun row ↦ do
          return .mk <$> Enum.fromHashMap? (← do
            let mut map := default
            for idx in Enum.all view.Index do
              if h : s!"{idx}" ∈ row then do
                match (view.name idx).column.ofRawValue? row[s!"{idx}"] with
                | some val => map := map.insert idx val
                | none => pure ()
              else
                pure ()
            return map)
    | .failure e => do
      IO.println s!"{repr e}"
      throw .fatal
    | _ => throw .fatal
  insert {table} data := do
    let conn := (← get).connection
    let sql : SQL.Insert := .fromInsert data
    _ ← conn.exec sql.toString
  delete _ :=
    throw .fatal

structure InformationSchema where
  table_name : VarChar 100
  column_name : VarChar 100
  is_nullable : Bool
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
      default? := info.column_default.bind fun d =>
        SQL.ColumnDefault.parse? dbtype (SQL.stripCast d) }

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

instance : DBMonadWithMigrations M where
  execute operation := do
    let conn := (← get).connection
    let sql : SQL.Migration.Operation := .fromDatabaseOperation operation
    IO.println s!"Executing {sql.toString}"
    let res ← conn.exec sql.toString
    match res with
    | .failure err =>
      IO.println s!"Error {repr err}"
      throw .fatal
    | .data _ =>
      IO.println s!"Returned data when no data was expected."
      throw .fatal
    | .success => pure ()
  currentDatabase := do
    let q : InformationSchema.model.Query :=
      .filter
        (.eq (.var InformationSchemaIndex.table_schema (.varchar 100))
                     (.str (v"public")))
        (.all _)
    let infos ← q.fetch
    let mut tables := .emptyWithCapacity
    for info in infos do
      if let some col := info.column then
      let table ← do
        if h : info.table_name.val ∈ tables then
          pure <| tables[info.table_name.val].columns.insert
            info.column_name.val col
        else
          pure <| { (info.column_name.val, col) }
      tables := tables.insert info.table_name.val { columns := table }
    return { tables := tables }

end PostgreSQL
