/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db
import Db.Backends.PostgreSQL.Interpretation

def main : IO Unit := do
  let q : Query database _ := .all "fish"
  let x : PostgreSQL.M _ := DBMonad.lookup q
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error _ => IO.println "Error occured."
  | .ok val =>
    let name : database.Name :=
      .ident { tableName := "fish", columnName := "name", column := ⟨.varchar 100⟩ }
    let x : name.dbtype.Value := val[0]!.get! name
    let x : VarChar 100 := x
    IO.println s!"Name of first fish is: {x}."
