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

## Query conditions

Inside a `query% do` block a `guard` is an ordinary Lean term over the bound row variables, which
is translated into an SQL condition. The following are recognised:

| Lean | SQL |
| --- | --- |
| `a.name = b.author`, `a.age ≠ 0` | `=`, `<>` |
| `a.age < 30`, `≤`, `>`, `≥` | `<`, `<=`, `>`, `>=` |
| `c₁ ∧ c₂`, `c₁ ∨ c₂`, `¬ c` (or `&&`, `\|\|`, `!`) | `AND`, `OR`, `NOT` |
| `b.year.isNone`, `b.year.isSome` | `IS NULL`, `IS NOT NULL` |
| `b.year = some 1998` | `= 1998` |
| `like b.title "A drama%"` | `LIKE 'A drama%'`, with `\\` escaping the next character |
| `contains b.title "100%"` | `LIKE '%100\\%%'`, with the wildcards in the needle escaped |
| `isIn a.name [v"Mike", v"Nora"]` | `IN ('Mike', 'Nora')` |

`like`, `contains` and `isIn` live in the `Db.Query.DSL` namespace and are only meaningful inside a
query block. In a `like` pattern `%` and `_` are wildcards and `\` escapes the character after it,
including itself, so a literal backslash is written `\\`; this is declared to the backend as
`ESCAPE '\'`, since PostgreSQL and SQLite disagree on the default. `contains` does that escaping
for you. A nullable column projects to an `Option`-valued field, so `some` is written around a
literal it is compared with; testing for `NULL` is `isNone`, not `= none`.

Membership in a subquery, `col IN (SELECT ...)`, is `DBExpr.inSubquery` on the core API; the
`query%` DSL has no surface syntax for it yet.

## Ordering, paging and aggregates

A `query% do` block can sort and page its result:

```lean4
query% do
  let b ← from Book
  guard b.author = v"Lisa"
  select b
  order_by b.title
  limit 10
  offset 20
```

`order_by`/`order_by_desc` may be repeated, in which case later keys break ties in earlier ones,
and may only name a column of the table given to `select`. The clauses are applied to the projected
result in the order `ORDER BY`, `OFFSET`, `LIMIT`, so a `limit` selects the first rows of the
sorted result. The same is available on a `QuerySet` as `.orderBy`, `.limit` and `.offset`.

`HasModel.count` counts the rows a query set matches without fetching them:

```lean4
IO.println s!"{← HasModel.count (QuerySet.all (α := Book))} books"
```

More general aggregation is `Query.aggregate`, which takes an `Aggregation source out`: every
column of the output view `out` is either a column of `source` that is grouped over, or an
aggregate (`COUNT(*)`, `COUNT`, `COUNT DISTINCT`, `SUM`, `MIN`, `MAX`) of the rows of a group. A
function is only applicable to the types it is defined on, so `SUM` over a `varchar` column does
not elaborate. Supplying the output view is what keeps this general — it names and types the
result columns, nullability included: grouping over a nullable column, or taking the `MIN` of one,
produces a column that can be `NULL`:

```lean4
def booksPerAuthor : Query mydb booksPerAuthorView :=
  .aggregate
    { entry
        | .author => .group BookIndex.author
        | .number => .countAll }
    (.all (HasModel.model Book).index)
```

`AVG` is missing because `DBType` has no floating-point type to give its result.

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
