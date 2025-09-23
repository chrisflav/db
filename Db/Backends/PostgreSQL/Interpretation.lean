/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Backends.PostgreSQL.Basic
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

instance (d : Database) : DBMonad d M where
  lookup {names} q := do
    let conn := (← get).connection
    let sql : SQL.Select := .fromQuery q
    let res ← conn.exec sql.toString
    match res with
    | .data data => data.rows.mapM <| fun map ↦ do
        let mut result := .emptyWithCapacity
        for pair in map do
          result := result.insert sorry sorry
        return result
    | _ => sorry

end PostgreSQL
