# A backend independent database client in Lean

This repository contains a relational database client library in Lean. The high-level interface
is backend and SQL independent. To give a brief impression, the following is an example:

```lean4
import Db

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

def drama : Book where
  title := v"A drama"
  author := lisa.name

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
  let res ← PostgreSQL.runDB "postgresql://username:password@localhost/database" x
  match res with
  | .error e => IO.println s!"Error occured: {repr e}."
  | .ok books =>
    for book in books do
      IO.println s!"Book {book.title} by {book.author}."
```

## Usage

Add this dependency to your project's `lakefile.toml`:

```toml
[[require]]
name = "Db"
git = "https://github.com/chrisflav/db"
rev = "master"
```

## Design

The library represents a database as an indexed family of tables, a table
as an indexed family of columns and a column as a supported database type.

To interact with a database, one can perform the standard operations (lookup, insert, delete)
in any monad implementing the class `DBMonad`.
Concrete backends, e.g. for PostgreSQL, provide monads over `IO` implementing `DBMonad`, so
that the general interface can be interpreted in any backend.

To connect an arbitrary type `α` to the language of `Database`, `Table` and `Column`,
there is the `Model` structure, bundling a table `t` and an equivalence of the entries of `t`
with `α`. The `@[model]` tag then automatically generates the required table and connection from
a `structure` and registers it as a table in the relevant database.
