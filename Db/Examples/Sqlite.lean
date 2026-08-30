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

/-- A hand-written schema exercising `text` columns and column defaults: a literal default, a call
default, a nullable column and a column with neither. -/
inductive NoteIndex where
  | id
  | body
  | state
  | archived
  | created
  | tag
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString NoteIndex where
  toString
    | .id => "id"
    | .body => "body"
    | .state => "state"
    | .archived => "archived"
    | .created => "created"
    | .tag => "tag"

instance : FromString NoteIndex where
  fromString
    | "id" => some .id
    | "body" => some .body
    | "state" => some .state
    | "archived" => some .archived
    | "created" => some .created
    | "tag" => some .tag
    | _ => none

instance : Indexing NoteIndex where

def noteTable : Table where
  Index := NoteIndex
  columns
    | .id => { type := .int, nullable := false, autoIncrement := true }
    | .body => { type := .text, nullable := false, default? := some (.str "") }
    | .state => { type := .varchar 20, nullable := false, default? := some (.str "open") }
    | .archived => { type := .bool, nullable := false, default? := some (.bool false) }
    | .created => { type := .int, nullable := false, default? := some (.call "unixepoch()") }
    | .tag => { type := .text, nullable := true }
  primaryKey := [.id]
  unique := [[.body, .state]]

/-- A join table: its two columns are its primary key together, and the first references `note`,
so deleting a note deletes the rows tagging it. -/
inductive NoteTagIndex where
  | noteId
  | tag
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString NoteTagIndex where
  toString
    | .noteId => "note_id"
    | .tag => "tag"

instance : FromString NoteTagIndex where
  fromString
    | "note_id" => some .noteId
    | "tag" => some .tag
    | _ => none

instance : Indexing NoteTagIndex where

def noteTagTable : Table where
  Index := NoteTagIndex
  columns
    | .noteId => { type := .int, nullable := false }
    | .tag => { type := .varchar 50, nullable := false }
  primaryKey := [.noteId, .tag]
  foreignKeys :=
    [{ columns := [.noteId]
       foreignTable := "note"
       foreignColumns := ["id"]
       onDelete := .cascade }]

inductive NoteDbIndex where
  | note
  | noteTag
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString NoteDbIndex where
  toString
    | .note => "note"
    | .noteTag => "note_tag"

instance : FromString NoteDbIndex where
  fromString
    | "note" => some .note
    | "note_tag" => some .noteTag
    | _ => none

instance : Indexing NoteDbIndex where

def noteDb : Database where
  Index := NoteDbIndex
  tables
    | .note => noteTable
    | .noteTag => noteTagTable

/-- The same schema with a different `UNIQUE` constraint, to migrate towards. -/
def noteDbAltered : DatabaseRecipe where
  tables := noteDb.recipe.tables.map fun name table =>
    if name == "note" then { table with unique := [["tag"]] } else table

/-- Exercise unbounded text and column defaults: create the schema, insert a row that omits every
column the database can fill in, insert one that supplies them, and confirm that the empty string
stays distinguishable from `NULL` and that the schema round-trips through introspection. -/
def defaultsDemo : Sqlite.M Unit := do
  autoUpdate noteDb.recipe
  -- Only `id` and `tag` are supplied; `body`, `state`, `archived` and `created` are left out of the
  -- statement so that the database fills in their defaults.
  DBMonad.insert (d := noteDb) (name := NoteDbIndex.note)
    { value
        | .id => some (1 : Int)
        | .body => none
        | .state => none
        | .archived => none
        | .created => none
        | .tag => some (some "urgent") }
  -- The second row supplies everything, including an empty `body` and a `NULL` `tag`.
  DBMonad.insert (d := noteDb) (name := NoteDbIndex.note)
    { value
        | .id => some (2 : Int)
        | .body => some ""
        | .state => some (v"closed")
        | .archived => some true
        | .created => some (0 : Int)
        | .tag => some none }
  let rows ← DBMonad.lookup (Query.all (d := noteDb) .note)
  IO.println "Notes:"
  for row in rows do
    letI body : String := row.value .body
    letI tag : Option String := row.value .tag
    letI created : Int := row.value .created
    IO.println <|
      s!"  id={row.value .id} body={repr body} state={row.value .state} " ++
      s!"archived={row.value .archived} tag={repr tag} " ++
      s!"created is set: {if 0 < created then "yes" else "no"}"
  -- The defaults have to survive introspection, or `autoUpdate` would keep trying to fix them.
  let pending := (← currentDatabase).operations noteDb.recipe
  IO.println s!"Pending operations after creating the schema: {pending.size}"

-- The parser has to recover what each database reports for a declared default, which is not the
-- text the default was declared with.

-- PostgreSQL reports a declared `DEFAULT -1` on an integer column as `'-1'::integer`.
#guard SQL.ColumnDefault.parse? .int (SQL.stripCast "'-1'::integer") == some (.int (-1))
-- SQLite reports an expression default with its parentheses already stripped, so an expression is
-- told from a string literal by whether its quotes are those of one.
#guard SQL.ColumnDefault.parse? .text "'a' || 'b'" == some (.call "'a' || 'b'")
#guard SQL.ColumnDefault.parse? .int "1+1" == some (.call "1+1")
#guard SQL.ColumnDefault.parse? .text "unixepoch()" == some (.call "unixepoch()")
#guard SQL.ColumnDefault.parse? .text "'it''s'" == some (.str "it's")
#guard SQL.ColumnDefault.parse? .text "''" == some (.str "")
#guard SQL.ColumnDefault.parse? .bool "false" == some (.bool false)

-- `DEFAULT NULL` supplies nothing a `NOT NULL` column can use, so it does not make one omittable,
-- and it declares nothing a column without a default does not already do, which is why PostgreSQL
-- discards it and the two have to compare equal.
#guard !({ type := .int, nullable := false, default? := some .null } : Column).isOptional
#guard ({ type := .int, nullable := false, default? := some (.int 0) } : Column).isOptional
#guard ({ type := .int, nullable := true, default? := some .null } : Column) ==
  ({ type := .int, nullable := true } : Column)

-- A `CREATE TABLE` carrying `REFERENCES` fails unless its target already exists, so the creations
-- have to come out in dependency order.
#guard (((∅ : DatabaseRecipe).operations noteDb.recipe).map fun op =>
    match op with
    | .insert name _ => name
    | _ => "?") == #["note", "note_tag"]

/-- The same schema with the type of a column of each table changed, which SQLite can realise only
by rebuilding both tables. -/
def noteDbRebuilt : DatabaseRecipe where
  tables := noteDb.recipe.tables.map fun name table =>
    let body : Column := { type := .varchar 100, nullable := false, default? := some (.str "") }
    let tag : Column := { type := .varchar 20, nullable := false }
    if name == "note" then { table with columns := table.columns.insert "body" body }
    else if name == "note_tag" then { table with columns := table.columns.insert "tag" tag }
    else table

/-- A schema SQLite cannot create: it only generates the value of a column that is exactly its
`INTEGER PRIMARY KEY`, and here the generated column is not the key. -/
def badKeyDb : DatabaseRecipe where
  tables := .ofList
    [("bad_key",
      { columns := .ofList
          [("k", { type := .int, nullable := false }),
           ("seq", { type := .int, nullable := false, autoIncrement := true })]
        primaryKey := ["k"] })]

/-- A table whose *name* contains `autoincrement`, which must not be mistaken for a generated key,
and one whose primary key is a nullable non-integer column, which SQLite really does allow. -/
def quirkDb : DatabaseRecipe where
  tables := .ofList
    [("autoincrement_log",
      { columns := .ofList [("x", { type := .int, nullable := false })]
        primaryKey := ["x"] }),
     ("nullable_key",
      { columns := .ofList
          [("x", { type := .varchar 10, nullable := true }),
           ("y", { type := .int, nullable := false })]
        primaryKey := ["x"] })]

/-- Exercise the constraints: an auto-incrementing primary key, a composite one, a `UNIQUE` group
and a cascading foreign key, all of which have to survive introspection, and a constraint change
that the migration machinery refuses rather than silently ignores. -/
def constraintsDemo : Sqlite.M Unit := do
  -- SQLite only enforces foreign keys when asked to.
  (← read).exec "PRAGMA foreign_keys = ON"
  autoUpdate noteDb.recipe
  DBMonad.insert (d := noteDb) (name := NoteDbIndex.note)
    { value
        | .id => none
        | .body => some "first"
        | .state => none
        | .archived => none
        | .created => none
        | .tag => none }
  DBMonad.insert (d := noteDb) (name := NoteDbIndex.note)
    { value
        | .id => none
        | .body => some "second"
        | .state => none
        | .archived => none
        | .created => none
        | .tag => none }
  -- The ids were assigned by the database, the insert having left them out.
  let notes ← DBMonad.lookup (Query.all (d := noteDb) .note)
  IO.println "Notes with generated ids:"
  for row in notes do
    let body : String := row.value .body
    let id : Int := row.value .id
    IO.println s!"  id={id} body={body}"
  for note in notes do
    DBMonad.insert (d := noteDb) (name := NoteDbIndex.noteTag)
      { value
          | .noteId => some ((note.value .id : Int))
          | .tag => some (v"urgent") }
  IO.println s!"Tag rows: {(← DBMonad.lookup (Query.all (d := noteDb) .noteTag)).size}"
  -- `ON DELETE CASCADE`: deleting a note takes its tag rows with it.
  let first : DBExpr noteDb (Table.view NoteDbIndex.note) .bool :=
    .eq (.var NoteIndex.id .int) (.int 1)
  IO.println s!"Deleted notes: {← DBMonad.delete (d := noteDb) { condition := first }}"
  let remaining ← DBMonad.lookup (Query.all (d := noteDb) .noteTag)
  IO.println s!"Tag rows after the cascade: {remaining.size}"
  -- The constraints have to survive introspection too.
  let pending := (← currentDatabase).operations noteDb.recipe
  IO.println s!"Pending operations after creating the schema: {pending.size}"
  IO.println s!"Constraint mismatches: {(← currentDatabase).constraintMismatches noteDb.recipe}"
  -- A constraint change on an existing table is reported rather than silently skipped.
  try
    autoUpdate noteDbAltered
    IO.println "Migrating the changed UNIQUE constraint was accepted, which it should not be."
  catch e =>
    IO.println s!"Refused, as expected: {e}"

/-- Rebuilding a table must carry its generated key and its foreign keys across, and must not be
blocked by the foreign keys of the tables referencing it. -/
def rebuildConstraintsDemo : Sqlite.M Unit := do
  (← read).exec "PRAGMA foreign_keys = ON"
  autoUpdate noteDb.recipe
  DBMonad.insert (d := noteDb) (name := NoteDbIndex.note)
    { value
        | .id => none
        | .body => some "first"
        | .state => none
        | .archived => none
        | .created => none
        | .tag => none }
  -- Changing a column's type is an `ALTER COLUMN`, which SQLite realises by rebuilding the table.
  autoUpdate noteDbRebuilt
  let current ← currentDatabase
  IO.println s!"Pending after the rebuild: {(current.operations noteDbRebuilt).size}"
  IO.println <|
    s!"Constraint mismatches after the rebuild: {current.constraintMismatches noteDbRebuilt}"
  let notes ← DBMonad.lookup (Query.all (d := noteDb) .note)
  IO.println s!"Rows preserved across the rebuild: {notes.size}"
  -- SQLite cannot generate the value of a column that is not its primary key.
  try
    autoUpdate badKeyDb
    IO.println "A generated non-key column was accepted, which it should not be."
  catch e =>
    IO.println s!"Refused, as expected: {e}"

/-- Two shapes the SQLite introspection used to read back wrongly: a table whose name contains
`autoincrement`, and a nullable non-integer primary key. Both have to reach a fixed point. -/
def quirkDemo : Sqlite.M Unit := do
  autoUpdate quirkDb
  let current ← currentDatabase
  IO.println s!"Pending for the quirky schema: {(current.operations quirkDb).size}"
  IO.println s!"Mismatches for the quirky schema: {current.constraintMismatches quirkDb}"
  -- A foreign key written without naming the referenced columns points at the target's primary
  -- key, and has to be read back as naming them.
  (← read).exec "CREATE TABLE par (a integer, b integer, PRIMARY KEY (a, b))"
  (← read).exec "CREATE TABLE chi (x integer, y integer, FOREIGN KEY (x, y) REFERENCES par)"
  let keys ← tableForeignKeys "chi"
  IO.println s!"Implicit reference read back as: {repr (keys.map (·.foreignColumns))}"

/-- Exercise `UPDATE`, `RETURNING` and transactions. -/
def writeDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  insert mike
  insert lisa
  insert nora
  -- `RETURNING` on an insert gives back the row the database stored, including the `id` it
  -- generated and the insert therefore left out.
  let urgent ← HasModel.insertReturning ({ id := 0, label := v"urgent" } : Tag)
  let later ← HasModel.insertReturning ({ id := 0, label := v"later" } : Tag)
  IO.println s!"Inserted tags: {urgent.id}={urgent.label}, {later.id}={later.label}"
  -- `UPDATE` setting one column on the rows a condition matches.
  let changed ← HasModel.update (α := Author)
    { value
        | .retired => some .true
        | _ => none
      condition := .lt (.var AuthorIndex.age .int) (.int 40) }
  IO.println s!"Retired {changed} author(s) under 40."
  -- `UPDATE ... RETURNING`, which gives back the rows as they now are.
  let renamed ← HasModel.updateReturning (α := Tag)
    { value
        | .label => some (.str (v"urgent!"))
        | _ => none
      condition := .eq (.var TagIndex.id .int) (.int urgent.id) }
  IO.println s!"Renamed: {renamed.map fun t => (t.id, t.label.val)}"
  -- `DELETE ... RETURNING`, which gives back the rows as they last were.
  let removed ← HasModel.deleteReturning (α := Tag)
    (.eq (.var TagIndex.id .int) (.int later.id))
  IO.println s!"Deleted: {removed.map fun t => (t.id, t.label.val)}"
  -- A transaction that fails leaves nothing behind.
  try
    DBMonadTransactional.withTransaction (m := Sqlite.M) do
      let _ ← HasModel.insertReturning ({ id := 0, label := v"doomed" } : Tag)
      let n ← HasModel.count (QuerySet.all (α := Tag))
      IO.println s!"Tags inside the transaction: {n}"
      throw (IO.userError "something went wrong")
  catch e =>
    IO.println s!"Transaction rolled back: {e}"
  IO.println s!"Tags after the rollback: {← HasModel.count (QuerySet.all (α := Tag))}"
  -- A transaction that succeeds commits.
  DBMonadTransactional.withTransaction (m := Sqlite.M) do
    let _ ← HasModel.insertReturning ({ id := 0, label := v"kept" } : Tag)
    pure ()
  -- A transaction nested in another is a savepoint, so its failure discards only its own work.
  DBMonadTransactional.withTransaction (m := Sqlite.M) do
    let _ ← HasModel.insertReturning ({ id := 0, label := v"outer" } : Tag)
    try
      DBMonadTransactional.withTransaction (m := Sqlite.M) do
        let _ ← HasModel.insertReturning ({ id := 0, label := v"inner" } : Tag)
        throw (IO.userError "the inner transaction failed")
    catch _ =>
      pure ()
  let afterInner ← fetch (QuerySet.all (α := Tag))
  IO.println s!"After a failed inner transaction: {afterInner.map (·.label.val)}"
  -- The outer one still discards everything, the inner one's work included.
  try
    DBMonadTransactional.withTransaction (m := Sqlite.M) do
      DBMonadTransactional.withTransaction (m := Sqlite.M) do
        let _ ← HasModel.insertReturning ({ id := 0, label := v"nested" } : Tag)
        pure ()
      throw (IO.userError "the outer transaction failed")
  catch _ =>
    pure ()
  let tags ← fetch (QuerySet.all (α := Tag))
  IO.println s!"Tags at the end: {tags.map (·.label.val)}"

/-- Initial schema: a `widget` table whose `label` is a nullable `varchar(50)`, next to a column
with an expression default. -/
def widgetV1 : DatabaseRecipe where
  tables := .ofList
    [("widget",
      { columns := .ofList
          [("id", { type := .int, nullable := false }),
           ("label", { type := .varchar 50, nullable := true }),
           ("created", { type := .int, nullable := false,
                         default? := some (.call "unixepoch()") })] })]

/-- Target schema: `label` is widened to a non-null `varchar(200)` and a `NOT NULL` column with an
expression default is added. SQLite can change neither a column in place nor add either of those,
so migrating to this schema forces a table rebuild, which has to carry the expression default of
`created` across intact. -/
def widgetV2 : DatabaseRecipe where
  tables := .ofList
    [("widget",
      { columns := .ofList
          [("id", { type := .int, nullable := false }),
           ("label", { type := .varchar 200, nullable := false }),
           ("created", { type := .int, nullable := false,
                         default? := some (.call "unixepoch()") }),
           ("kind", { type := .varchar 20, nullable := false,
                      default? := some (.call "upper('x')") })] })]

/-- Demonstrate an `ALTER COLUMN` migration: create `widget`, insert a row, then migrate the `label`
column's type and nullability (via a table rebuild) and confirm the data survives. -/
def migrationDemo : Sqlite.M Unit := do
  autoUpdate widgetV1
  (← read).exec "INSERT INTO widget (id, label) VALUES (1, 'hello')"
  IO.println "Migrating `widget.label`: varchar(50) NULL -> varchar(200) NOT NULL ..."
  autoUpdate widgetV2
  let rows ← query "SELECT id, label, kind, created > 0 AS c FROM widget ORDER BY id"
  IO.println "Rows after migration (data preserved across the rebuild):"
  for row in rows do
    IO.println <|
      s!"  id={row.textD "id" "?"}, label={row.textD "label" "?"}, " ++
      s!"kind={row.textD "kind" "?"}, created is set={row.textD "c" "?"}"
  -- The migration is idempotent: re-running against the same target yields no further operations.
  let pending := (← currentDatabase).operations widgetV2
  IO.println s!"Pending operations after migration: {pending.size}"

/-- Run both demos against a fresh in-memory SQLite database. -/
def test : IO Unit := do
  Sqlite.runDB ":memory:" bookDemo
  Sqlite.runDB ":memory:" operatorDemo
  Sqlite.runDB ":memory:" shapeDemo
  Sqlite.runDB ":memory:" defaultsDemo
  Sqlite.runDB ":memory:" constraintsDemo
  Sqlite.runDB ":memory:" rebuildConstraintsDemo
  Sqlite.runDB ":memory:" quirkDemo
  Sqlite.runDB ":memory:" writeDemo
  Sqlite.runDB ":memory:" migrationDemo

end SqliteExample
