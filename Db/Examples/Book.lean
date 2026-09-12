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

/-- Conflict handling against a real server: PostgreSQL is stricter than SQLite about `ON CONFLICT`,
requiring a conflict target for `DO UPDATE`, so the generated statement is worth running there. -/
def conflictTest : IO Unit := do
  let x : PostgreSQL.M Unit := do
    autoUpdate (%database mydb)
    let _ ← HasModel.delete (α := Tag) .true
    let tag (id : Int) (label : VarChar 50) :
        (HasModel.database Tag).Insert (HasModel.model Tag).index :=
      { value
          | TagIndex.id => some id
          | TagIndex.label => some label }
    DBMonad.insert (d := HasModel.database Tag) (tag 1 (v"urgent"))
    let ignored ← DBMonad.insertReturning (d := HasModel.database Tag)
      { tag 1 (v"ignored") with onConflict := .ignore }
    IO.println s!"Rows stored by the ignored insert (PostgreSQL): {ignored.size}"
    let updated ← DBMonad.insertReturning (d := HasModel.database Tag)
      { tag 1 (v"upserted") with onConflict := .update [TagIndex.id] [TagIndex.label] }
    IO.println <|
      s!"Rows stored by the upserting insert (PostgreSQL): {updated.size}, " ++
      s!"label now {(updated[0]?.map (fun e => toString (e.value TagIndex.label))).getD "?"}"
  match ← PostgreSQL.runDB "postgresql://testuser:secret@localhost/testdb2" x with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok _ => pure ()

/-- The left outer join against a real server. -/
def leftJoinTest : IO Unit := do
  let x : PostgreSQL.M Unit := do
    autoUpdate (%database mydb)
    let _ ← HasModel.delete (α := Book) .true
    let _ ← HasModel.delete (α := Author) .true
    insert mike
    insert novel
    insert { title := v"Anonymous", author := v"Nobody", year := none : Book }
    let joined : Query (%database mydb) _ :=
      .leftJoin (.all (HasModel.model Book).index) (.all (HasModel.model Author).index)
        (.eq (.var (Sum.inl BookIndex.author) (.varchar 100))
             (.var (Sum.inr AuthorIndex.name) (.varchar 100)))
    let rows ← DBMonad.lookup joined
    IO.println "Books with their author, left-joined (PostgreSQL):"
    for row in rows do
      IO.println <|
        s!"  {row.value (Sum.inl BookIndex.title)} — " ++
        s!"author age {row.value (Sum.inr AuthorIndex.age)}"
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
