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

abbrev initial : MigrationRecipe ∅ where
  operations :=
    #[.insert "author"
      { columns := .ofArray #[
          ("age", { type := .int, nullable := true })
        ]
      }
    ]

abbrev mig1 : MigrationRecipe initial.execute where
  operations :=
    #[.alter "author" (.rename "age" "age21"),
      .alter "author" (.rename "age21" "age"),
    ]

abbrev mig2 : MigrationRecipeWithTarget mig1.execute database.recipe where
  operations := mig1.execute.operations database.recipe

end Migrations

def test : IO Unit := do
  let mike : Author :=
    { name := v"Mike"
      age := 34
      retired := false }
  let q : QuerySet authorModel := Query.all authorModel.index
  let x : PostgreSQL.M _ := do
    DBMonadWithMigrations.execute (.remove "author")
    DBMonadWithMigrations.executeMany initial.operations
    DBMonadWithMigrations.executeMany mig1.operations
    DBMonadWithMigrations.executeMany mig2.operations
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok _ => IO.println "Migration successful."

end BookExample
