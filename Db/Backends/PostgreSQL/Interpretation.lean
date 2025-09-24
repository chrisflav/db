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
  if ht : tableName ∈ d.tables then
    if hc : columnName ∈ d.tables[tableName].columns then
      some (.ident { tableName := tableName, columnName := columnName })
    else
      none
  else
    none

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
        --let mut rows := #[]
        --for i in Fin.range data.nrows do
        --  let row : Std.DHashMap d.Name fun n => n.dbtype.Value ← do
        --    let mut map := default
        --    for name in names do
        --      map := map.insert name _
        --    pure map
        --  rows := rows.push row
        --return rows
    | _ => throw .fatal

/-
    data.rows.mapM <| fun map ↦ do
        let mut result := .emptyWithCapacity
        for (name, value) in map do
          match name.splitOn "." with
          | [tableName, columnName] =>
              match d.resolveName tableName columnName with
              | some (.ident i) =>
                match value with
                | .raw s => _
                | .int n => _
                | .bool b => result := result.insert (.ident i) (unsafeCast b)
                | .string s => result := result.insert (.ident i) (unsafeCast s)
                --have heq : (Database.Name.ident i).dbtype.Value = VarChar 100 := sorry
                --result := result.insert (.ident i) sorry
              | _ => pure ()
          | _ => pure ()
        return result
    -/

end PostgreSQL
