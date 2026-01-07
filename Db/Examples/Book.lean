/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

namespace BookExample

structure Author where
  name : VarChar 100
  age : Int
  retired : Bool
  deriving Repr

generate_table BookExample.Author

inductive Index where
  | author
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString Index where
  toString
    | .author => "author"

instance : FromString Index where
  fromString
    | "author" => some .author
    | _ => none

instance : Indexing Index where

def database : Database where
  Index := Index
  tables
    | .author => AuthorTable

instance : HasTable Author (database.tables .author) :=
  inferInstanceAs <| HasTable Author AuthorTable

def authorModel : Model database Author where
  index := .author

section Migrations

def filePath : System.FilePath :=
  "migrations" / "book"

abbrev initial : Array DatabaseOperation :=
  #[.insert "author"
    { columns := .ofArray #[
        ("age21", { type := .int, nullable := false })
      ]
    }
  ]

abbrev initial.result : DatabaseRecipe :=
  HasExecution.execute ∅ initial[0] <| by grind

abbrev mig1 : Array DatabaseOperation :=
  #[.alter "author"
    (.alter "age" { type := .int, nullable := false })
  ]

-- TODO: add (grind) API to prove certain operations preserve validity
def mig1.result : DatabaseRecipe :=
  HasExecution.execute initial.result mig1[0] sorry

end Migrations

def test : IO Unit := do
  let mike : Author :=
    { name := v"Mike"
      age := 34
      retired := false }
  let q : QuerySet authorModel := Query.all authorModel.index
  let x : PostgreSQL.M _ := do
    let d ← DBMonadWithMigrations.currentDatabase
    for op in d.operations database.recipe do
      IO.println (repr op)
    q.fetch
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok authors =>
    for author in authors do
      IO.println s!"Fetched author {repr author}."

end BookExample
