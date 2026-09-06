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

## Joins

`Query.join` is a cross join, and an inner join is that filtered by a condition, which is what the
`query%` DSL writes for a `guard` relating two bound rows.

An outer join is not that, and cannot be built out of it: a `WHERE` runs after the join has already
decided which rows found no partner, so no condition over a cross product keeps a row that matched
nothing. `Query.leftJoin` carries its own condition and is a constructor of its own:

```lean
-- Every book, with its author where there is one.
let joined : Query mydb _ :=
  .leftJoin (.all (HasModel.model Book).index) (.all (HasModel.model Author).index)
    (.eq (.var (Sum.inl BookIndex.author) (.varchar 100))
         (.var (Sum.inr AuthorIndex.name) (.varchar 100)))
```

The result view is `s.prod t.nullable`: the join makes every column of the right-hand side
nullable, so `row.value (Sum.inr AuthorIndex.age)` is an `Option Int` even though `age` is declared
`NOT NULL`, and is `none` for a book whose author has no row. Like `inSubquery`, this is core API
that the `query%` DSL has no surface syntax for yet.

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

## Column types and defaults

`DBType` covers `bool`, `int`, `varchar n` and unbounded `text`. A model field of type `String`
becomes a `text` column, `Option α` a nullable one.

A column may declare a `default?`, which the database fills in when an insert omits it:

```lean4
def noteTable : Table where
  Index := NoteIndex
  columns
    | .id => { type := .int, nullable := false }
    | .body => { type := .text, nullable := false, default? := some (.str "") }
    | .state => { type := .varchar 20, nullable := false, default? := some (.str "open") }
    | .created => { type := .int, nullable := false, default? := some (.call "unixepoch()") }
    | .tag => { type := .text, nullable := true }
```

A `Database.Insert` supplies a value for each column or `none` to leave it to the database; a
column may only be left out if it has a default or is nullable, which is a side condition of the
structure discharged by `rfl`. `Database.Insert.ofEntry` builds the insert that supplies
everything, which is what the model layer uses.

`DEFAULT NULL` declares nothing a column without a default does not already do, so it does not make
a `NOT NULL` column omittable and compares equal to no default at all — which is what PostgreSQL
reports back, having discarded it.

The SQL text of a `.call` default is passed to the backend unchanged, so it has to be a call the
target database knows — `unixepoch()` is SQLite's, PostgreSQL spells it differently. Defaults are
read back by schema introspection so that `autoUpdate` reaches a fixed point. Since a database
rewrites the text of an expression default when it reports it back (PostgreSQL reports a declared
`abs(-1)` as `abs('-1'::integer)`), two expression defaults are compared as equal, and a change to
one is not migrated.

Values read from a database keep `NULL` apart from the empty string: the backends use the driver's
null flag rather than treating an empty result as `NULL`, which matters as soon as a column holds
unbounded text.

## Keys and constraints

A `Table` declares a primary key, groups of columns that are unique together, and foreign keys:

```lean4
def noteTagTable : Table where
  Index := NoteTagIndex
  columns
    | .noteId => { type := .int, nullable := false }
    | .tag => { type := .varchar 50, nullable := false }
  primaryKey := [.noteId, .tag]
  foreignKeys :=
    [{ columns := [.noteId], foreignTable := "note", foreignColumns := ["id"]
       onDelete := .cascade }]
```

The referencing columns are indices of the table, the referenced ones strings, since a `Table` does
not know the database it belongs to.

A column may be `autoIncrement`, meaning the database assigns its value; `Database.Insert.ofEntry`
leaves such a column out, so the model layer never sends one. In a model structure a field of type
`AutoKey` becomes exactly that — an auto-incrementing single-column primary key:

```lean4
@[model (dbName := "tag") mydb]
structure Tag where
  id : AutoKey
  label : VarChar 50
```

`CREATE TABLE` renders these per dialect, since the two backends spell a generated key differently
(`INTEGER PRIMARY KEY AUTOINCREMENT` against `GENERATED BY DEFAULT AS IDENTITY`), and both backends
read all of it back so that `autoUpdate` reaches a fixed point. SQLite only generates the value of
a column that is exactly its `INTEGER PRIMARY KEY`, so a schema whose generated column is not its
whole primary key is refused there rather than created with a key nobody declared. Table creations
are ordered so that a table comes after the tables its foreign keys reference, and drops in the
reverse.

The operation language describes column changes only, so a **constraint change on an existing
table is not migrated**. Rather than applying such a migration as a silent no-op, `autoUpdate`
aborts and names the tables whose constraints differ; migrate those by hand, or drop and recreate
them.

## Writing

`DBMonad` covers the four statements, each in a plain form and one that returns the affected rows:

| | | |
| --- | --- | --- |
| `lookup` | `q : Query d view` | `Array view.Entry` |
| `insert` / `insertReturning` | `d.Insert name` | `Unit` / the rows stored |
| `update` / `updateReturning` | `d.Update name` | rows changed / the rows as they now are |
| `delete` / `deleteReturning` | `d.Delete name` | rows deleted / the rows as they last were |

`Database.Update` sets each column to the value of an expression over the row being updated, or
leaves it alone, on the rows a condition matches. `Database.Delete` names the table it deletes from
rather than deriving it from the columns its condition happens to mention: SQL deletes from one
table, and a condition over a join view names columns that are only in scope inside a subquery.

The model layer wraps these as `HasModel.insertReturning`, `.update`, `.updateReturning`, `.delete`
and `.deleteReturning`. `insertReturning` is how the value of a column the database generates is
obtained without a second query:

```lean4
let tag ← HasModel.insertReturning ({ id := 0, label := v"urgent" } : Tag)
IO.println s!"the database assigned id {tag.id}"
```

`DBMonadTransactional.withTransaction` groups several operations into one atomic unit, committing
if the block succeeds and rolling back if it fails. A nested call is a savepoint, so its failure
discards only its own work while an outer failure still discards everything. On PostgreSQL only a
failure of the backend's own exception type rolls back; an `IO` error thrown underneath escapes
with the transaction still open.

A caveat on identifiers: DDL emits them unquoted, so PostgreSQL folds a mixed-case column name to
lower case while SQLite keeps it. Queries and returning statements are unaffected, as both alias
their columns, but schema introspection on PostgreSQL then reports the folded name and `autoUpdate`
does not converge. Keep column names lower case for now.

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
