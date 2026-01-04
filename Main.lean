/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db
import Db.Examples.Fish
import Db.Examples.Book
import Db.Backends.PostgreSQL.Interpretation

open FishExample in
def testManual : IO Unit := do
  let nameIdent : database.Ident :=
    { tableName := .fish, columnName := .name, column := ⟨.varchar 100, false⟩ }
  let name : database.Name :=
    .ident { tableName := .fish, columnName := .name, column := ⟨.varchar 100, false⟩ }
  let lengthIdent : database.Ident :=
    { tableName := .fish, columnName := .length, column := ⟨.int, false⟩ }
  let length : database.Name :=
    .ident lengthIdent
  let ins : database.Insert .fish :=
    { entry.values
        | .name => ⟨"Aal", by decide⟩
        | .length => 56 }
  let q : Query database _ :=
    .filter
      (.all DatabaseIndex.fish)
      (.eq (.var nameIdent (.varchar 100)) (.str ⟨"Aal", by decide⟩))
  let x : PostgreSQL.M _ := do
    _ ← DBMonad.insert ins
    DBMonad.lookup q
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error _ => IO.println "Error occured."
  | .ok val =>
    for row in val do
      let x : VarChar 100 := row.get! name
      let l : Int := row.get! length
      IO.println s!"Fish {x} has length {l}."

open BookExample in
def main : IO Unit := do
  let mike : Author :=
    { name := v"Mike"
      age := 34
      retired := false }
  let q : QuerySet authorModel := Query.all authorModel.index
  let x : PostgreSQL.M _ := do
    authorModel.insert mike
    q.fetch
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error _ => IO.println "Error occured."
  | .ok authors =>
    for author in authors do
      IO.println s!"Fetched author {repr author}."
