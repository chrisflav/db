/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Book

/-!
# SQLite backend example

The same workflow as the PostgreSQL `BookExample`, but running against the SQLite backend. Because
SQLite is embedded, this runs end to end against an in-memory database without any external server:
the schema is created via `autoUpdate`, rows are inserted, a join query written with the query DSL is
fetched back, rows are deleted, and a column-type migration is applied.
-/

namespace SqliteExample

open BookExample Sqlite HasModel DBMonadWithMigrations

/-- Create the schema, insert some rows, fetch every book by a retired author, then delete rows. -/
def bookDemo : Sqlite.M Unit := do
  -- Create the `author` and `book` tables to match the declared schema.
  autoUpdate (%database mydb)
  -- Insert some data.
  insert mike
  insert lisa
  insert novel
  insert drama
  -- Fetch all books whose author is retired, using the query DSL.
  let retired ← fetch <| query% do
    let a ← from Author
    let b ← from Book
    guard b.author = a.name
    guard a.retired
    select b
  IO.println "Books by retired authors (SQLite backend):"
  for book in retired do
    IO.println s!"  {book.title} by {book.author}"
  -- Delete every book written by Mike and report how many rows were removed.
  let removed ← HasModel.delete (α := Book)
    (.eq (.var BookIndex.author (.varchar 100)) (.str mike.name))
  IO.println s!"Deleted {removed} book(s) by {mike.name}."
  -- Show what remains.
  let remaining ← fetch (QuerySet.all (α := Book))
  IO.println "Remaining books:"
  for book in remaining do
    IO.println s!"  {book.title} by {book.author}"

/-- Initial schema: a `widget` table whose `label` is a nullable `varchar(50)`. -/
def widgetV1 : DatabaseRecipe where
  tables := .ofList
    [("widget", { columns := .ofList [("id", ⟨.int, false⟩), ("label", ⟨.varchar 50, true⟩)] })]

/-- Target schema: `label` is widened to a non-null `varchar(200)`. SQLite cannot change a column in
place, so migrating to this schema forces a table rebuild. -/
def widgetV2 : DatabaseRecipe where
  tables := .ofList
    [("widget", { columns := .ofList [("id", ⟨.int, false⟩), ("label", ⟨.varchar 200, false⟩)] })]

/-- Demonstrate an `ALTER COLUMN` migration: create `widget`, insert a row, then migrate the `label`
column's type and nullability (via a table rebuild) and confirm the data survives. -/
def migrationDemo : Sqlite.M Unit := do
  autoUpdate widgetV1
  (← read).exec "INSERT INTO widget (id, label) VALUES (1, 'hello')"
  IO.println "Migrating `widget.label`: varchar(50) NULL -> varchar(200) NOT NULL ..."
  autoUpdate widgetV2
  let rows ← query "SELECT id, label FROM widget ORDER BY id"
  IO.println "Rows after migration (data preserved across the rebuild):"
  for row in rows do
    IO.println s!"  id={row.getD "id" "?"}, label={row.getD "label" "?"}"
  -- The migration is idempotent: re-running against the same target yields no further operations.
  let pending := (← currentDatabase).operations widgetV2
  IO.println s!"Pending operations after migration: {pending.size}"

/-- Run both demos against a fresh in-memory SQLite database. -/
def test : IO Unit := do
  Sqlite.runDB ":memory:" bookDemo
  Sqlite.runDB ":memory:" migrationDemo

end SqliteExample
