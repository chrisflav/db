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
