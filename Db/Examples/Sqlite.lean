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

open BookExample Sqlite HasModel DBMonadWithMigrations Db.Query.DSL

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

/-- A third author, and two more books, so the operator demo below has something to discriminate. -/
def nora : Author where
  name := v"Nora"
  age := 41
  retired := false

def percent : Book where
  title := v"100% pure"
  author := nora.name
  year := some 2011

def sequel : Book where
  title := v"A drama, the sequel"
  author := lisa.name
  year := some 2020

/-- Exercise the comparison, boolean, null-test, `LIKE` and `IN` operators end to end. Each block
prints the rows the corresponding SQL returned. -/
def operatorDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  insert mike
  insert lisa
  insert nora
  insert novel
  insert drama
  insert percent
  insert sequel
  -- Ordering comparisons on an integer column.
  let older ← fetch <| query% do
    let a ← from Author
    guard a.age > (40 : Int)
    select a
  IO.println s!"Authors over 40: {older.map (·.name.val)}"
  -- `OR`, and a `<` in the other operand.
  let either ← fetch <| query% do
    let a ← from Author
    guard a.retired ∨ a.age < (30 : Int)
    select a
  IO.println s!"Retired or under 30: {either.map (·.name.val)}"
  -- `NOT`.
  let active ← fetch <| query% do
    let a ← from Author
    guard ¬ a.retired
    select a
  IO.println s!"Not retired: {active.map (·.name.val)}"
  -- `IS NULL` and `IS NOT NULL`, written on the `Option`-valued field of a nullable column.
  let undated ← fetch <| query% do
    let b ← from Book
    guard b.year.isNone
    select b
  IO.println s!"Books without a year: {undated.map (·.title.val)}"
  let dated ← fetch <| query% do
    let b ← from Book
    guard b.year.isSome
    guard b.year ≠ (some 1998 : Option Int)
    select b
  IO.println s!"Books with a year other than 1998: {dated.map (·.title.val)}"
  -- `LIKE`, with the pattern written out, and with the wildcards in the needle escaped.
  let dramas ← fetch <| query% do
    let b ← from Book
    guard like b.title "A drama%"
    select b
  IO.println s!"Titles starting with \"A drama\": {dramas.map (·.title.val)}"
  -- `%` in the needle has to match a literal `%`, not act as a wildcard.
  let literal ← fetch <| query% do
    let b ← from Book
    guard contains b.title "100%"
    select b
  IO.println s!"Titles containing \"100%\": {literal.map (·.title.val)}"
  -- `IN` over a literal list.
  let listed ← fetch <| query% do
    let a ← from Author
    guard isIn a.name [v"Mike", v"Nora"]
    select a
  IO.println s!"Authors named Mike or Nora: {listed.map (·.name.val)}"
  -- `IN (SELECT ...)`: the books whose author is one of the retired authors. Written against the
  -- core API, since the `query%` DSL has no surface syntax for a subquery.
  let byRetired ← fetch (α := Book)
    { query :=
        .filter
          (.inSubquery (.var BookIndex.author (.varchar 100))
            (.filter (.eq (.var AuthorIndex.retired .bool) .true)
              (.all (HasModel.model Author).index))
            AuthorIndex.name)
          (.all _) }
  IO.println s!"Books by a retired author (via subquery): {byRetired.map (·.title.val)}"

/-- The output view of "how many books does each author have": the grouped `author` column next to
the number of rows in each group. -/
inductive BooksPerAuthorIndex where
  | author
  | number
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString BooksPerAuthorIndex where
  toString
    | .author => "author"
    | .number => "number"

instance : FromString BooksPerAuthorIndex where
  fromString
    | "author" => some .author
    | "number" => some .number
    | _ => none

instance : Indexing BooksPerAuthorIndex where

def booksPerAuthorView : View (%database mydb) where
  Index := BooksPerAuthorIndex
  name
    | .author => .computation "author" { type := .varchar 100, nullable := false }
    | .number => .computation "number" { type := .int, nullable := false }

/-- `SELECT author, COUNT(*) FROM book GROUP BY author`. -/
def booksPerAuthor : Query (%database mydb) booksPerAuthorView :=
  .aggregate
    { entry
        | .author => .group BookIndex.author
        | .number => .countAll }
    (.all (HasModel.model Book).index)

/-- The output view of "how many books were published in each year". `year` is nullable in `book`,
so the column grouping over it has to be nullable too: the group of the books with no year is a
row of the result like any other. -/
inductive BooksPerYearIndex where
  | year
  | number
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString BooksPerYearIndex where
  toString
    | .year => "year"
    | .number => "number"

instance : FromString BooksPerYearIndex where
  fromString
    | "year" => some .year
    | "number" => some .number
    | _ => none

instance : Indexing BooksPerYearIndex where

def booksPerYearView : View (%database mydb) where
  Index := BooksPerYearIndex
  name
    | .year => .computation "year" { type := .int, nullable := true }
    | .number => .computation "number" { type := .int, nullable := false }

/-- `SELECT year, COUNT(*) FROM book GROUP BY year`. -/
def booksPerYear : Query (%database mydb) booksPerYearView :=
  .aggregate
    { entry
        | .year => .group BookIndex.year
        | .number => .countAll }
    (.all (HasModel.model Book).index)

-- `MIN`/`MAX` are defined on character data, so this entry has to elaborate; `SUM` over the same
-- column does not, since `AggregateFn.appliesTo` rules it out.
example : AggregateEntry (Table.view (HasModel.model Book).index) :=
  .apply .max BookIndex.title

/-- Exercise sorting, paging and aggregation end to end. -/
def shapeDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  insert mike
  insert lisa
  insert nora
  insert novel
  insert drama
  insert percent
  insert sequel
  -- `ORDER BY`, ascending and descending.
  let sorted ← fetch <| query% do
    let b ← from Book
    select b
    order_by b.title
  IO.println s!"Books by title: {sorted.map (·.title.val)}"
  let reversed ← fetch <| query% do
    let b ← from Book
    select b
    order_by_desc b.title
  IO.println s!"Books by title, descending: {reversed.map (·.title.val)}"
  -- `LIMIT`, and `LIMIT` with `OFFSET`, applied to the sorted result.
  let firstTwo ← fetch <| query% do
    let b ← from Book
    select b
    order_by b.title
    limit 2
  IO.println s!"First two by title: {firstTwo.map (·.title.val)}"
  let window ← fetch <| query% do
    let b ← from Book
    select b
    order_by b.title
    limit 2
    offset 1
  IO.println s!"Two books from the second on: {window.map (·.title.val)}"
  -- `OFFSET` without a `LIMIT`, which SQLite only accepts with one supplied.
  let skipped ← fetch
    ((QuerySet.all (α := Book)).orderBy [{ column := BookIndex.title }] |>.offset 3)
  IO.println s!"All but the first three by title: {skipped.map (·.title.val)}"
  -- Sorting by two keys, the second breaking ties in the first.
  let byAuthor ← fetch
    ((QuerySet.all (α := Book)).orderBy [{ column := BookIndex.author },
      { column := BookIndex.title, direction := .desc }])
  IO.println s!"By author, then title descending: {byAuthor.map (·.title.val)}"
  -- `COUNT(*)` of a whole table, and of a filtered query set.
  IO.println s!"Number of books: {← HasModel.count (QuerySet.all (α := Book))}"
  let dated : QuerySet Book :=
    { query := .filter (.isNotNull (.var BookIndex.year .int)) (.all _) }
  IO.println s!"Number of books with a year: {← HasModel.count dated}"
  -- `COUNT(*)` grouped by author.
  let grouped ← DBMonad.lookup booksPerAuthor
  IO.println "Books per author:"
  for row in grouped do
    IO.println s!"  {row.value .author} wrote {row.value .number} book(s)"
  -- Grouping over a nullable column: the group of the rows with no year is a row of the result.
  let perYear ← DBMonad.lookup booksPerYear
  IO.println "Books per year:"
  for row in perYear do
    letI year : Option Int := row.value .year
    IO.println s!"  {repr year}: {row.value .number} book(s)"
  -- Filtering an aggregate applies to the aggregated rows, not to the rows it aggregates.
  let prolific ← DBMonad.lookup
    (Query.filter (.gt (.var BooksPerAuthorIndex.number .int) (.int 1)) booksPerAuthor)
  IO.println s!"Authors with more than one book: {prolific.map fun r => (r.value .author).val}"
  -- Sorting an already sorted query breaks its ties by the earlier sort.
  let tiebroken ← fetch
    ((QuerySet.all (α := Book)).orderBy [{ column := BookIndex.title, direction := .desc }]
      |>.orderBy [{ column := BookIndex.author }])
  IO.println s!"By author, ties by title descending: {tiebroken.map (·.title.val)}"

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
  Sqlite.runDB ":memory:" operatorDemo
  Sqlite.runDB ":memory:" shapeDemo
  Sqlite.runDB ":memory:" migrationDemo

end SqliteExample
