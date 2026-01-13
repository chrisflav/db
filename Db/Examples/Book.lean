/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

namespace BookExample

initialize_database mydb

@[model (dbName := "author") mydb]
structure Author where
  name : VarChar 100
  age : Int
  retired : Bool
  deriving Repr

@[model (dbName := "book") mydb]
structure Book where
  title : VarChar 200
  author : VarChar 100
  deriving Repr

open HasModel DBMonadWithMigrations

-- TODO: add query DSL, supporting join queries
def test : IO Unit := do
  let mike : Author :=
    { name := v"Mike"
      age := 74
      retired := true }
  let lisa : Author :=
    { name := v"Lisa"
      age := 27
      retired := false }
  let novel : Book :=
    { title := v"Best novel ever!"
      author := mike.name  }
  let drama : Book :=
    { title := v"A drama"
      author := lisa.name  }
  let x : PostgreSQL.M (Array Author) := do
    -- Update database schema to target schema
    autoUpdate (%database mydb)
    -- Insert `mike` into the `Author` table
    insert mike
    insert lisa
    -- Insert `novel` into the `Book` table
    insert novel
    insert drama
    -- Print all books
    for book in (← fetch .all) do
      IO.println s!"Book: {Book.title book}"
    -- Fetch all authors from the `Author` table.
    fetch .all
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok authors =>
    for author in authors do
      IO.println s!"{author.name} has age {author.age}."

end BookExample
