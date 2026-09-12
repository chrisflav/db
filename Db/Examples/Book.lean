/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Postgres
import Db.Examples.Schema

/-!
# PostgreSQL backend example

The same schema as `Db.Examples.Sqlite`, run against a PostgreSQL server. Needs one listening at
the connection string below, which is why this is not part of `lake test`.
-/

namespace BookExample

open HasModel DBMonadWithMigrations Db.Query.DSL

/-- The `mydb` schema with indexes on `book`, named through the model's own index type: one plain,
one descending, one case-insensitive over two keys, and one unique. -/
def indexedRecipe : DatabaseRecipe :=
  (%database mydb).recipe.withIndexes "book" <| tableIndexes BookIndex
    [ { name := "idx_book_author", keys := [{ column := .author }] },
      { name := "idx_book_year_desc", keys := [{ column := .year, direction := .desc }] },
      { name := "idx_book_title_nocase",
        keys := [{ column := .title, collation := .caseInsensitive }, { column := .author }] },
      { name := "idx_book_title_unique", keys := [{ column := .title }], unique := true } ]

/-- Indexes against a real server. Worth its own demo because PostgreSQL hands an index definition
back in its own spelling rather than the one it was given — a `lower(title)` on a `varchar` column
comes back as `lower((title)::text)` — and `autoUpdate` only converges if that is read back as what
was declared. -/
def indexTest : IO Unit := do
  let x : PostgreSQL.M Unit := do
    -- The demo above leaves its rows behind, and re-running it leaves them twice, so the unique
    -- index below would have nothing to be unique over. Start from an empty table.
    autoUpdate (%database mydb)
    let _ ← HasModel.delete (α := Book) .true
    autoUpdate indexedRecipe
    let pending := (← currentDatabase).indexOperations indexedRecipe
    IO.println s!"Pending index operations after creating them (PostgreSQL): {pending.size}"
    let current ← currentDatabase
    for idx in (current.tables["book"]?.map (·.indexes)).getD [] do
      IO.println s!"  read back: {repr idx}"
  match ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok _ => pure ()

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
