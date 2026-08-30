/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

namespace BookExample

initialize_database mydb

/-- A book author. -/
@[model (dbName := "author") mydb]
structure Author where
  name : VarChar 100
  age : Int
  retired : Bool
  deriving Repr

/-- A book. -/
@[model (dbName := "book") mydb]
structure Book where
  title : VarChar 200
  author : VarChar 100
  /-- The year of publication, unknown for some books. -/
  year : Option Int
  deriving Repr

/-- A tag, whose `id` the database assigns: `AutoKey` makes it a single-column auto-incrementing
primary key, which an insert leaves out. -/
@[model (dbName := "tag") mydb]
structure Tag where
  id : AutoKey
  label : VarChar 50
  deriving Repr

open HasModel DBMonadWithMigrations

def mike : Author where
  name := v"Mike"
  age := 74
  retired := true

def lisa : Author where
  name := v"Lisa"
  age := 27
  retired := false

def novel : Book where
  title := v"Best novel ever!"
  author := mike.name
  year := some 1998

def drama : Book where
  title := v"A drama"
  author := lisa.name
  year := none

section DSLChecks

open Db.Query.DSL

/-- A term over a binder of the enclosing definition is a constant of the query, and is embedded as
a literal. -/
def booksBy (name : VarChar 100) : QuerySet Book := query% do
  let b ← from Book
  guard b.author = name
  select b

-- A term the DSL cannot translate has to be reported as such, even when it has the type of a
-- database value: embedding it would let a row variable escape the query block.
/--
error: unsupported expression in query condition: `a.age + 1`
-/
#guard_msgs in
-- An `example`, not a `def`: the failed elaboration leaves a `sorry` behind, which as a compiled
-- top-level constant would abort the executable at load time.
example : QuerySet Author := query% do
  let a ← from Author
  guard a.age + 1 > (5 : Int)
  select a

end DSLChecks

def test : IO Unit := do
  let x : PostgreSQL.M (Array Book) := do
    -- Update database schema to target schema
    autoUpdate (%database mydb)
    -- Insert some data into the database
    insert mike
    insert lisa
    insert novel
    insert drama
    -- Fetch all books that have a retired author.
    fetch <| query% do
      let a ← from Author
      let b ← from Book
      guard b.author = a.name
      guard a.retired
      select b
  let res ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok books =>
    for book in books do
      IO.println s!"Book {book.title} by {book.author}."

end BookExample
