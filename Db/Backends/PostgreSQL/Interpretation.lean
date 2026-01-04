/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Backends.PostgreSQL.Basic
import Db.Utils.FromString
import Db.Backends.Sql
import Db.Interpretation.Basic

def Database.resolveName (d : Database) (tableName columnName : String) : Option d.Name :=
  match (FromString.fromString tableName : Option d.Index) with
  | some tableName =>
    match (FromString.fromString columnName : Option (d.tables tableName).Index) with
    | some columnName => some (.ident { tableName := tableName, columnName := columnName })
    | none => none
  | none => none

namespace PostgreSQL

inductive Exception where
  | fatal

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
  | none => return .error .fatal

instance (d : Database) : DBMonad d M where
  lookup {names} q := do
    let conn := (← get).connection
    let sql : SQL.Select := .fromQuery q
    let res ← conn.exec sql.toString
    match res with
    | .data data =>
        data.rawRows.mapM <| fun row ↦ do
          let mut map := default
          for name in names do
            if h : name.toString ∈ row then do
              let x := row[name.toString]
              match (FromString.fromString row[name.toString] :
                  Option name.dbtype.Value) with
              | some val => map := map.insert name val
              | none => pure ()
            else
              pure ()
          return map
    | _ => throw .fatal
  insert {table} data := do
    let conn := (← get).connection
    let sql : SQL.Insert := .fromInsert data
    _ ← conn.exec sql.toString
  delete _ :=
    throw .fatal

instance : DBMonadWithMigrations M where
  createTable name table := do
    let conn := (← get).connection
    let sql : SQL.Migration.CreateTable := .fromTable table name
    _ ← conn.exec sql.toString

end PostgreSQL
