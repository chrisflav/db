/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Postgres
import Db.Examples.Schema
import Db.Examples.Migrations

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
  match ← PostgreSQL.runDB (← postgresUrl) x with
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
  match ← PostgreSQL.runDB (← postgresUrl) x with
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
  match ← PostgreSQL.runDB (← postgresUrl) x with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok _ => pure ()

/-- The correlated scalar subquery against a real server. -/
def correlateTest : IO Unit := do
  let x : PostgreSQL.M Unit := do
    autoUpdate (%database mydb)
    let _ ← HasModel.delete (α := Book) .true
    let _ ← HasModel.delete (α := Author) .true
    insert mike
    insert lisa
    insert novel
    insert drama
    let counted : Query (%database mydb) _ :=
      .correlate "books"
        (.all (HasModel.model Author).index)
        (.all (HasModel.model Book).index)
        (.eq (.var (Sum.inr BookIndex.author) (.varchar 100))
             (.var (Sum.inl AuthorIndex.name) (.varchar 100)))
        .countAll
    IO.println "Authors and how many books they wrote (PostgreSQL):"
    for row in ← DBMonad.lookup counted do
      IO.println s!"  {row.value (Sum.inl AuthorIndex.name)}: {row.value (Sum.inr ⟨⟩)}"
  match ← PostgreSQL.runDB (← postgresUrl) x with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok _ => pure ()

/-- A computed column, filtered on. PostgreSQL is the backend that has anything to say here: a
`WHERE` naming an alias of its own `SELECT` list is an SQLite extension and a plain error on
PostgreSQL, so the condition has to be applied to a select that already exposes the computed
column. -/
def extendTest : IO Unit := do
  let x : PostgreSQL.M Unit := do
    autoUpdate (%database mydb)
    let _ ← HasModel.delete (α := Author) .true
    insert mike
    insert lisa
    let inTenYears : Query (%database mydb) _ :=
      .extend "age_in_10" { type := .int, nullable := false }
        (.add (.var AuthorIndex.age .int) (.int 10))
        (.all (HasModel.model Author).index)
    let over50 : Query (%database mydb) _ :=
      .filter (.gt (.var (Sum.inr (⟨⟩ : IUnit "age_in_10")) .int) (.int 50)) inTenYears
    IO.println "Authors over 50 in ten years (PostgreSQL):"
    for row in ← DBMonad.lookup over50 do
      IO.println s!"  {row.value (Sum.inl AuthorIndex.name)}: {row.value (Sum.inr ⟨⟩)}"

/-- The declarative migrations against a real server.

Worth running there and not only on SQLite: the two migrations are the same Lean value on both, so
this is what shows that "declare once, apply anywhere" holds — the raw `UPDATE` of the second
migration, the foreign key of the first, and the `DESC` index all have to be understood by
PostgreSQL as well.

Unlike the in-memory SQLite database, this one persists between runs and is shared with the other
demos, so the demo drops what it created at both ends: at the start so that a re-run starts from no
migrations applied, and at the end so that the next demo's `autoUpdate` does not find tables its
target does not declare and drop them. -/
def migrationsTest : IO Unit := do
  let drop : PostgreSQL.M Unit := do
    -- `mig_writer` is what `renameDemo` leaves `mig_author` called.
    for table in ["mig_book", "mig_tag", "mig_author", "mig_writer", "db_migrations"] do
      DBMonadWithMigrations.rawExecute s!"DROP TABLE IF EXISTS {table}"
  let x : PostgreSQL.M Unit := do
    drop
    MigrationExample.migrationsDemo "PostgreSQL"
    -- A migration the database records that the code does not declare stops `migrate`.
    MigrationExample.recordUnknownMigration
    try
      let _ ← Db.Migration.migrate MigrationExample.migrations 1700000002
      IO.println "  a recorded-but-unknown migration was accepted, which it should not be."
    catch _ =>
      IO.println "  refused, as expected."
    MigrationExample.forgetUnknownMigration
    -- The renames, whose point is that the folded schema follows them the way the database does.
    MigrationExample.renameDemo MigrationExample.migrations
    drop
  match ← PostgreSQL.runDB (← postgresUrl) x with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok _ => pure ()

/-- Identifier quoting against a real server. This is the backend the issue was about: PostgreSQL
folds an unquoted identifier to lower case, so before the quoting a column declared `addedAt` was
stored as `addedat`, introspection read back a name the target schema did not have, and
`autoUpdate` proposed to add `addedAt` again on every run — it never converged. The reserved words
`order` and `select` did not get that far at all; they were syntax errors. -/
def identifierTest : IO Unit := do
  let x : PostgreSQL.M Unit := do
    autoUpdate readingListDb
    -- Re-runs of the suite find the rows the last one left, and the demo prints them.
    let _ ← HasModel.delete (α := ReadingList) .true
    insert gatsby
    insert moby
    IO.println "Reading list (PostgreSQL):"
    for row in ← fetch (QuerySet.all (α := ReadingList)) do
      IO.println <|
        s!"  order={row.order} addedAt={row.addedAt} select={row.select} {row.bookTitle}"
    -- The fixed point that used never to be reached: with the declared case preserved, a second
    -- `autoUpdate` against the same target has nothing left to do, indexes included.
    autoUpdate readingListDb
    let current ← currentDatabase
    IO.println <|
      s!"Pending operations after two autoUpdates (PostgreSQL): " ++
      s!"{(current.operations readingListDb).size}, " ++
      s!"index operations: {(current.indexOperations readingListDb).size}"
    for idx in (current.tables["readingList"]?.map (·.indexes)).getD [] do
      IO.println s!"  read back: {repr idx}"
    let moved ← HasModel.updateReturning (α := ReadingList)
      { value
          | .order => some (.int 99)
          | _ => none
        condition := .eq (.var ReadingListIndex.addedAt .int) (.int moby.addedAt) }
    IO.println s!"Updated (PostgreSQL): {moved.map fun r => (r.bookTitle.val, r.order)}"
    let dropped ← HasModel.deleteReturning (α := ReadingList)
      (.var ReadingListIndex.select .bool)
    IO.println s!"Deleted the selected row(s) (PostgreSQL): {dropped.map (·.bookTitle.val)}"
  match ← PostgreSQL.runDB (← postgresUrl) x with
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
  let res ← PostgreSQL.runDB (← postgresUrl) x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok books =>
    for book in books do
      IO.println s!"Book {book.title} by {book.author}."

end BookExample
