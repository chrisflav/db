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
  let database := HasModel.database Author
  let authorModel := HasModel.model Author
  let bookModel := HasModel.model Book
  /-
  let q : QuerySet Book ← do
    all where author.retired = true
  -/
  let q : QuerySet Book :=
    { query :=
      Query.project (View.sumInr _ _) <|
      Query.filter (.eq (.var (Sum.inl AuthorIndex.retired) .bool) .true) <|
      Query.filter
        (.eq (.var (Sum.inl AuthorIndex.name) (.varchar 100))
             (.var (Sum.inr BookIndex.author) (.varchar 100)))
        (Query.join (.all <| authorModel.index) (.all <| bookModel.index)) }
  -- IO.println (SQL.Select.fromQuery q).toString
  let x : PostgreSQL.M (Array Book) := do
    -- Update database schema to target schema
    -- autoUpdate (%database mydb)
    -- Insert `mike` into the `Author` table
    -- insert mike
    -- insert lisa
    -- Insert `novel` into the `Book` table
    -- insert novel
    -- insert drama
    -- Print all books
    -- for book in (← fetch .all) do
    --   IO.println s!"Book: {Book.title book}"
    -- Fetch all authors from the `Author` table.
    -- fetch .all
    fetch q
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok books =>
    for book in books do
      IO.println s!"Book {book.title} by {book.author}."

end BookExample
