/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Schema
import Db.Examples.Migrations
import Db.Examples.Joins
import Db.Examples.Recursive
import Db.Examples.Floats
import Db.Examples.Keys

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
  -- Case-insensitive ordering. `aBSOLUTE` sorts between `A drama` and `Best novel ever!` under
  -- `nocase`, and after every capitalised title without it.
  insert { title := v"aBSOLUTE beginners", author := lisa.name, year := none : Book }
  let caseSensitive ← fetch <| query% do
    let b ← from Book
    select b
    order_by b.title
  IO.println s!"By title, case-sensitively: {caseSensitive.map (·.title.val)}"
  let caseInsensitive ← fetch <| query% do
    let b ← from Book
    select b
    order_by b.title nocase
  IO.println s!"By title, ignoring case: {caseInsensitive.map (·.title.val)}"
  -- Null placement. `year` is `NULL` for two of these, and SQLite would sort them first ascending.
  let nullsLast ← fetch <| query% do
    let b ← from Book
    select b
    order_by b.year nulls_last
  IO.println s!"By year, nulls last: {nullsLast.map (fun b => (b.year, b.title.val))}"
  let nullsFirstDesc ← fetch <| query% do
    let b ← from Book
    select b
    order_by_desc b.year nulls_first
  IO.println <|
    s!"By year descending, nulls first: {nullsFirstDesc.map (fun b => (b.year, b.title.val))}"
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

/-- The note schema with indexes declared on it: one plain, one descending, one case-insensitive,
and one unique. -/
def noteDbIndexed : DatabaseRecipe where
  tables := noteDb.recipe.tables.map fun name table =>
    if name == "note" then
      { table with
          indexes :=
            [ { name := "idx_note_state", keys := [{ column := "state" }] },
              { name := "idx_note_created_desc",
                keys := [{ column := "created", direction := .desc }] },
              { name := "idx_note_body_nocase",
                keys := [{ column := "body", collation := .caseInsensitive },
                         { column := "id" }] },
              { name := "idx_note_tag_unique", keys := [{ column := "tag" }], unique := true } ] }
    else table

/-- The same, with `idx_note_state` re-declared over a different column, to migrate towards. -/
def noteDbIndexedAltered : DatabaseRecipe where
  tables := noteDbIndexed.tables.map fun name table =>
    if name == "note" then
      { table with
          indexes := table.indexes.map fun idx =>
            if idx.name == "idx_note_state" then
              { idx with keys := [{ column := "archived" }] }
            else idx }
    else table

/-- Exercise index support: create the schema with indexes, confirm they reach the database and
round-trip through introspection, then change one and confirm it is re-created. -/
def indexDemo : Sqlite.M Unit := do
  autoUpdate noteDbIndexed
  let listed ← query <|
    "SELECT name AS nm, sql AS ddl FROM sqlite_master WHERE type = 'index' " ++
    "AND sql IS NOT NULL ORDER BY name"
  IO.println "Indexes in the database:"
  for row in listed do
    IO.println s!"  {row.textD "ddl" "?"}"
  -- Reaching a fixed point is the whole point: introspection has to read back exactly what was
  -- declared, or every run would drop and re-create the same indexes.
  let pending := (← currentDatabase).indexOperations noteDbIndexed
  IO.println s!"Pending index operations after creating them: {pending.size}"
  -- An index whose keys changed is dropped and re-created under the same name.
  autoUpdate noteDbIndexedAltered
  let after ← query <|
    "SELECT sql AS ddl FROM sqlite_master WHERE type = 'index' AND name = 'idx_note_state'"
  IO.println s!"After re-declaring it: {(after[0]?.map (·.textD "ddl" "?")).getD "(gone)"}"
  IO.println <|
    s!"Pending index operations after the change: " ++
    s!"{((← currentDatabase).indexOperations noteDbIndexedAltered).size}"
  -- An index the target does not declare is left alone rather than dropped.
  (← read).exec "CREATE INDEX idx_note_handmade ON note (state, id)"
  let stillThere := ((← currentDatabase).indexOperations noteDbIndexedAltered).size
  autoUpdate noteDbIndexedAltered
  let handmade ← query <|
    "SELECT count(*) AS n FROM sqlite_master WHERE type = 'index' AND name = 'idx_note_handmade'"
  IO.println <|
    s!"A hand-made index survives autoUpdate: {handmade[0]!.textD "n" "?"} " ++
    s!"(and provoked {stillThere} operations)"
  -- PostgreSQL reports an ascending key without the `ASC` it was given, so the whole of such a
  -- key's text is the column name and the direction keywords are only recognised when a separator
  -- puts them outside it. Without that a column called `basc` reads back as `b` and its index
  -- never converges. The parser is shared, so SQLite is where it is cheapest to check.
  let parsed : String → String := fun sql =>
    match SQL.Migration.parseCreateIndex? "i" sql with
    | some idx => ", ".intercalate (idx.keys.map fun k => s!"{k.column} {repr k.direction}")
    | none => "(unparsed)"
  IO.println s!"PostgreSQL spelling `(basc)`: {parsed "CREATE INDEX i ON t USING btree (basc)"}"
  IO.println <|
    s!"PostgreSQL spelling `(recdesc DESC)`: " ++
    s!"{parsed "CREATE INDEX i ON t USING btree (recdesc DESC)"}"

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
  let printNotes (header : String) : Sqlite.M Unit := do
    let rows ← DBMonad.lookup (Query.all (d := noteDb) .note)
    IO.println header
    for row in rows do
      letI body : String := row.value .body
      letI tag : Option String := row.value .tag
      letI created : Int := row.value .created
      IO.println <|
        s!"  id={row.value .id} body={repr body} state={row.value .state} " ++
        s!"archived={row.value .archived} tag={repr tag} " ++
        s!"created is set: {if 0 < created then "yes" else "no"}"
  printNotes "Notes:"
  -- A `text` column is compared with a literal at its own type: `eq` has both operands at one
  -- `DBType`, and `DBExpr.str` is the bounded one, at `varchar n`.
  let urgent ← DBMonad.lookup
    (Query.filter (.eq (.var NoteIndex.tag .text) (.text "urgent")) (Query.all (d := noteDb) .note))
  IO.println s!"Notes tagged \"urgent\": {urgent.map fun row => (row.value NoteIndex.id : Int)}"
  -- The same literal on the right of an `UPDATE ... SET`, for a `text` column and for a nullable
  -- one, on the row the condition picks out.
  let changed ← DBMonad.update (d := noteDb) (name := NoteDbIndex.note)
    { value
        | .body => some (.text "edited")
        | .tag => some (.text "later")
        | _ => none
      condition := .eq (.var NoteIndex.id .int) (.int 2) }
  IO.println s!"Updated {changed} note(s) with text literals."
  printNotes "Notes after the update:"
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

/-- Exercise conflict handling on insert: a second row conflicting with the first is skipped when
the insert says to ignore it, and overwrites the stored one when the insert says to update. -/
def conflictDemo : Sqlite.M Unit := do
  autoUpdate noteDb.recipe
  let note (id : Int) (body : String) (state : VarChar 20) :
      (noteDb).Insert NoteDbIndex.note :=
    { value
        | .id => some id
        | .body => some body
        | .state => some state
        | .archived => none
        | .created => none
        | .tag => none }
  DBMonad.insert (d := noteDb) (note 1 "first" (v"open"))
  -- `id` is the primary key, so this conflicts. Without a conflict action it would fail.
  let ignored ← DBMonad.insertReturning (d := noteDb)
    { note 1 "second" (v"open") with onConflict := .ignore }
  IO.println s!"Rows stored by the ignored insert: {ignored.size}"
  let rows ← query "SELECT body FROM note WHERE id = 1"
  IO.println s!"The row is untouched: {rows[0]!.textD "body" "?"}"
  -- The same conflict, resolved by overwriting `body` with the value the insert carried.
  let updated ← DBMonad.insertReturning (d := noteDb)
    { note 1 "third" (v"open") with onConflict := .update [.id] [.body] }
  IO.println s!"Rows stored by the upserting insert: {updated.size}"
  let rows ← query "SELECT body, state FROM note WHERE id = 1"
  IO.println <|
    s!"The row was overwritten: body={rows[0]!.textD "body" "?"}, " ++
    s!"state={rows[0]!.textD "state" "?"} (untouched, not in the set list)"
  -- An insert that supplies no column at all is `DEFAULT VALUES`, which SQLite lets no
  -- `ON CONFLICT` follow, so `.ignore` is spelled `INSERT OR IGNORE` there. Two such rows conflict
  -- with each other on the `UNIQUE (body, state)` group, since both take the same defaults.
  let blank : (noteDb).Insert NoteDbIndex.note := { value := fun _ => none }
  IO.println <|
    s!"SQL: {(SQL.Insert.fromInsert { blank with onConflict := .ignore }).toString .sqlite}"
  DBMonad.insert (d := noteDb) blank
  let ignoredBlank ← DBMonad.insertReturning (d := noteDb) { blank with onConflict := .ignore }
  IO.println s!"Rows stored by the second all-defaults insert: {ignoredBlank.size}"
  -- `DO UPDATE` has no spelling after `DEFAULT VALUES` at all, so the backend says so rather than
  -- sending SQLite a statement it will reject.
  try
    DBMonad.insert (d := noteDb) { blank with onConflict := .update [.id] [.body] }
    IO.println "  an upserting all-defaults insert was accepted, which it should not be."
  catch e =>
    IO.println s!"  refused, as expected: {e}"

/-- Exercise the left outer join: every book, with its author's row where there is one and `NULL`
throughout the author's columns where there is not. -/
def leftJoinDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  insert mike
  insert novel
  -- No author row for this one, so it is the book whose author columns come back `NULL`.
  insert { title := v"Anonymous", author := v"Nobody", year := none : Book }
  let bookTable := (HasModel.model Book).index
  let authorTable := (HasModel.model Author).index
  let joined : Query (%database mydb) _ :=
    .leftJoin (.all bookTable) (.all authorTable)
      (.eq (.var (Sum.inl BookIndex.author) (.varchar 100))
           (.var (Sum.inr AuthorIndex.name) (.varchar 100)))
  let rows ← DBMonad.lookup joined
  IO.println "Books with their author, left-joined:"
  for row in rows do
    letI title := row.value (Sum.inl BookIndex.title)
    letI age := row.value (Sum.inr AuthorIndex.age)
    IO.println s!"  {title} — author age {age}"

/-- Exercise the correlated scalar subquery: every author, with the number of books they wrote,
counted by a subquery rather than by a join that would drop the authors who wrote none. -/
def correlateDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  insert mike
  insert lisa
  insert nora
  insert novel
  insert drama
  insert sequel
  let counted : Query (%database mydb) _ :=
    .correlate "books"
      (.all (HasModel.model Author).index)
      (.all (HasModel.model Book).index)
      (.eq (.var (Sum.inr BookIndex.author) (.varchar 100))
           (.var (Sum.inl AuthorIndex.name) (.varchar 100)))
      .countAll
  IO.println s!"SQL: {(SQL.Select.fromQuery counted).toString}"
  let rows ← DBMonad.lookup counted
  IO.println "Authors and how many books they wrote:"
  for row in rows do
    IO.println <|
      s!"  {row.value (Sum.inl AuthorIndex.name)}: {row.value (Sum.inr ⟨⟩)}"
  -- An aggregate other than a count. `MAX` over no rows is `NULL`, so the column is nullable and
  -- the author who wrote nothing reads back as `none` rather than as a zero.
  let latest : Query (%database mydb) _ :=
    .correlate "latest"
      (.all (HasModel.model Author).index)
      (.all (HasModel.model Book).index)
      (.eq (.var (Sum.inr BookIndex.author) (.varchar 100))
           (.var (Sum.inl AuthorIndex.name) (.varchar 100)))
      (.apply .max BookIndex.year)
  IO.println "Authors and the year of their latest book:"
  for row in ← DBMonad.lookup latest do
    IO.println <|
      s!"  {row.value (Sum.inl AuthorIndex.name)}: {row.value (Sum.inr ⟨⟩)}"

/-- Exercise computed columns and arithmetic: a column that is not read from a table but worked
out from the row it belongs to. -/
def extendDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  insert mike
  insert lisa
  insert nora
  let inTenYears : Query (%database mydb) _ :=
    .extend "age_in_10" { type := .int, nullable := false }
      (.add (.var AuthorIndex.age .int) (.int 10))
      (.all (HasModel.model Author).index)
  IO.println "Authors and their age in ten years:"
  for row in ← DBMonad.lookup inTenYears do
    IO.println <|
      s!"  {row.value (Sum.inl AuthorIndex.name)}: " ++
      s!"{row.value (Sum.inl AuthorIndex.age)} -> {row.value (Sum.inr ⟨⟩)}"
  -- Filtering on the computed column. The condition cannot name the alias the column is given:
  -- an alias of the same `SELECT` list is in scope in a `WHERE` on SQLite but not on PostgreSQL.
  -- The translation substitutes the expression the column is computed from into the condition
  -- instead, which is why the SQL below has no subquery and repeats the arithmetic.
  let over50 : Query (%database mydb) _ :=
    .filter (.gt (.var (Sum.inr (⟨⟩ : IUnit "age_in_10")) .int) (.int 50)) inTenYears
  IO.println s!"SQL: {(SQL.Select.fromQuery over50).toString}"
  IO.println "Those over 50 by then:"
  for row in ← DBMonad.lookup over50 do
    IO.println s!"  {row.value (Sum.inl AuthorIndex.name)}: {row.value (Sum.inr ⟨⟩)}"

section ModelConflicts

-- A second database, so that the demos above keep the schema they had.
initialize_database labeldb

/-- A label, keyed by its name rather than by a generated id, so that an insert carries the column
a conflict is decided on. -/
@[model (dbName := "label") labeldb]
structure Label where
  name : VarChar 50
  colour : VarChar 20
  deriving Repr

/-- A memo, whose only content is a `String` field — an unbounded `text` column, which is what the
`query%` DSL needs `DBExpr.text` for: a condition on it compares it with a literal at `text`. -/
@[model (dbName := "memo") labeldb]
structure Memo where
  id : AutoKey
  text : String
  deriving Repr

/-- `name` is unique, by an index declared on the recipe: `@[model]` generates no indexes, and an
`AutoKey` would be no use here — the database assigns it, so the insert leaves it out and no row
ever conflicts on it. -/
def labelDb : DatabaseRecipe :=
  (%database labeldb).recipe.withIndexes "label" <| tableIndexes LabelIndex
    [{ name := "idx_label_name", keys := [{ column := .name }], unique := true }]

/-- Exercise the model-level conflict helpers against a key the row actually carries. -/
def modelConflictDemo : Sqlite.M Unit := do
  autoUpdate labelDb
  let first ← HasModel.insertIfAbsent ({ name := v"urgent", colour := v"red" } : Label)
  let again ← HasModel.insertIfAbsent ({ name := v"urgent", colour := v"green" } : Label)
  IO.println s!"insertIfAbsent, then the same label again: {first}, {again}"
  let rows ← HasModel.upsert ({ name := v"urgent", colour := v"blue" } : Label)
    [LabelIndex.name] [LabelIndex.colour]
  IO.println <|
    s!"upsert stored {rows.size} row(s), colour now " ++
    s!"{(rows[0]?.map (·.colour.val)).getD "?"}"
  -- A `text` column in the DSL: a `String` constant is embedded as `DBExpr.text`, and `like` and
  -- `contains` take a `text` column as readily as a `varchar n` one.
  let hello ← HasModel.insertReturning ({ id := 0, text := "hello" } : Memo)
  let world ← HasModel.insertReturning ({ id := 0, text := "world" } : Memo)
  IO.println s!"Inserted memos: {hello.id}={hello.text}, {world.id}={world.text}"
  let exact ← fetch <| query% do
    let m ← from Memo
    guard m.text = "hello"
    select m
  IO.println s!"Memos equal to \"hello\": {exact.map (·.text)}"
  let substring ← fetch <| query% do
    let m ← from Memo
    guard contains m.text "ell"
    select m
  IO.println s!"Memos containing \"ell\": {substring.map (·.text)}"
  let prefixed ← fetch <| query% do
    let m ← from Memo
    guard like m.text "h%"
    select m
  IO.println s!"Memos matching \"h%\": {prefixed.map (·.text)}"

end ModelConflicts

/-- A hand-written table with two defaults on float columns. `ColumnDefault` has no floating-point
literal — it derives `DecidableEq` and `Hashable`, and `Float` has neither — so a fractional
default is an expression, and what makes an expression converge is the comparison rather than the
text: `BEq Column`, which the migration diff uses, holds any two `.call` defaults to be equal,
however the database rewrites the text of one. An integer default is a literal like any other, and
has to come back as the `.int` it was declared as.

A database of its own, which only the SQLite suite can afford: `autoUpdate` drops the tables its
target does not declare, and every demo here runs against a fresh in-memory database. -/
def gaugeDb : DatabaseRecipe where
  tables := .ofList
    [("gauge",
      { columns := .ofList
          [("id", { type := .int, nullable := false }),
           ("reading", { type := .float, nullable := false, default? := some (.call "0.0") }),
           -- An integer literal is a default a float column can have — both dialects widen it —
           -- and it has to be read back as the `.int` it was declared as. Parsed as an expression
           -- it would differ from the declaration on every run.
           ("offset", { type := .float, nullable := false, default? := some (.int 0) })]
        primaryKey := ["id"] })]

/-- `save` on a model with no primary key has nothing to conflict on, so it says so rather than
storing a second row that looks like the first. `Book` is such a model: ordinary columns, no
declared key and no `AutoKey` field. -/
def saveWithoutKeyDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  try
    HasModel.save novel
    IO.println "a keyless save was accepted, which it should not be."
  catch e =>
    IO.println s!"refused, as expected: {e}"

/-- `save` on a model whose key the database generates is refused too, and for a subtler reason:
there *is* a key, so the upsert is built and runs, but the insert leaves the generated column out,
nothing conflicts on it, and every call appends a row. `Tag` is such a model — a single `AutoKey`
field. The table has to be empty afterwards, or the refusal came too late to be one. -/
def saveWithGeneratedKeyDemo : Sqlite.M Unit := do
  autoUpdate (%database mydb)
  for _ in [0:2] do
    try
      HasModel.save ({ id := 0, label := v"urgent" } : Tag)
      IO.println "a save on a generated key was accepted, which it should not be."
    catch e =>
      IO.println s!"refused, as expected: {e}"
  IO.println s!"rows in `tag` after two saves: {← HasModel.count (QuerySet.all (α := Tag))}"

/-- A default on a float column reaches a fixed point too: the expression default of `reading` and
the integer one of `offset` both have to come back as what was declared, or `autoUpdate` proposes
the same `ALTER COLUMN` for ever and `makemigrations` writes a migration that changes nothing. -/
def floatDefaultDemo : Sqlite.M Unit := do
  autoUpdate gaugeDb
  autoUpdate gaugeDb
  let current ← currentDatabase
  let pending := (current.operations gaugeDb).size
  IO.println s!"pending operations on `gauge` after two autoUpdates: {pending}"
  unless pending == 0 do
    throw <| IO.userError <|
      s!"two autoUpdates against `gaugeDb` left {pending} operation(s) pending, so a float " ++
      "default does not round-trip"
  let readBack : String → String := fun column =>
    s!"{repr ((current.tables["gauge"]?.bind (·.columns[column]?)).map fun c => (c.type, c.default?))}"
  IO.println s!"the type and default read back for `gauge`.`reading`: {readBack "reading"}"
  IO.println s!"the type and default read back for `gauge`.`offset`: {readBack "offset"}"

/-- Change `mig_book.year` from an integer to text. SQLite realises a column type change by
rebuilding the table, which is why this exists in two versions: the atomic one cannot work there,
and saying so is the point. -/
def yearAsText (atomic : Bool) : Db.Migration.Migration where
  name := "0003_year_as_text"
  steps := [.alterColumn "mig_book" "year" { type := .varchar 10, nullable := true }]
  atomic := atomic

/-- The declarative migrations on SQLite: the shared demo, then the two refusals — a migration the
database records and the code does not declare, and a column type change in an atomic migration. -/
def migrationsDemo : Sqlite.M Unit := do
  MigrationExample.migrationsDemo "SQLite"
  -- A migration the database records that the code does not declare means the database is ahead of
  -- the code, which `migrate` refuses to build on.
  MigrationExample.recordUnknownMigration
  try
    let _ ← Db.Migration.migrate MigrationExample.migrations 1700000002
    IO.println "  a recorded-but-unknown migration was accepted, which it should not be."
  catch e =>
    IO.println s!"  refused, as expected: {e}"
  MigrationExample.forgetUnknownMigration
  -- The SQLite rule: a column type change rebuilds the table, and a rebuild cannot happen inside a
  -- transaction, so the atomic version has to refuse before it has done anything.
  try
    let _ ← Db.Migration.migrate (MigrationExample.migrations ++ [yearAsText true]) 1700000003
    IO.println "  an atomic rebuild was accepted, which it should not be."
  catch e =>
    IO.println s!"  refused, as expected: {e}"
  IO.println s!"  recorded after the refusal: {← Db.Migration.applied (m := Sqlite.M)}"
  let applied ← Db.Migration.migrate (MigrationExample.migrations ++ [yearAsText false]) 1700000004
  IO.println s!"  the same migration with atomic := false applied: {applied}"
  let current ← currentDatabase
  IO.println <|
    s!"  mig_book.year is now " ++
    s!"{repr ((current.tables["mig_book"]?.bind (·.columns["year"]?)).map (·.type))}"
  IO.println s!"  rows preserved across the rebuild: {(← query "SELECT * FROM mig_book").size}"
  -- SQLite realises an `ADD COLUMN` of a `NOT NULL` column without a default by a rebuild too, and
  -- that is the step `makemigrations` writes for a new non-optional model field, so the comment
  -- `render` puts above the plan has to cover it as well as `alterColumn`.
  let notNullPlan :=
    Db.Migration.render "0005_x"
      [.addColumn "mig_book" "sold" { type := .int, nullable := false }]
  IO.println <|
    s!"  render warns about a NOT NULL addColumn: " ++
    s!"{MigrationExample.occurs notNullPlan "atomic := false"}"
  -- An atomic migration records itself before it runs its steps, so that a second `migrate` racing
  -- it fails on the primary key of the tracking table instead of applying everything twice. The
  -- record is inside the transaction, so a migration that fails still leaves nothing behind.
  try
    let _ ← Db.Migration.migrate
      (MigrationExample.migrations ++ [yearAsText false, MigrationExample.failingMigration])
      1700000900
    IO.println "  a failing migration was accepted, which it should not be."
  catch _ =>
    IO.println "  the failing migration was rolled back, as expected."
  let afterFailure ← currentDatabase
  IO.println <|
    s!"  recorded after the rollback: {← Db.Migration.applied (m := Sqlite.M)}, " ++
    s!"its first step's table: {afterFailure.tables.contains "mig_never"}"
  MigrationExample.renameDemo (MigrationExample.migrations ++ [yearAsText false])
  MigrationExample.dropColumnDemo (MigrationExample.migrations ++ [yearAsText false])

/-- Exercise identifier quoting: a table whose name and columns are mixed-case and include two
reserved words. Everything the library emits is double-quoted, so the names survive as declared and
`autoUpdate` converges — which is the point of the quoting, and what PostgreSQL used to fail at
because it folds an unquoted identifier to lower case. SQLite keeps the case either way, so what
this checks here is that the quoted SQL is accepted at all, that the reserved words are usable as
names, and that an index over a quoted column reads back as the one that was declared. -/
def identifierDemo : Sqlite.M Unit := do
  autoUpdate readingListDb
  IO.println s!"SQL: {(SQL.Select.fromQuery (QuerySet.all (α := ReadingList)).query).toString}"
  insert gatsby
  insert moby
  IO.println "Reading list (SQLite):"
  for row in ← fetch (QuerySet.all (α := ReadingList)) do
    IO.println <|
      s!"  order={row.order} addedAt={row.addedAt} select={row.select} {row.bookTitle}"
  -- The fixed point: a second `autoUpdate` against the same target has nothing left to do, columns
  -- and indexes alike. A mixed-case column read back folded would be proposed again on every run.
  autoUpdate readingListDb
  let current ← currentDatabase
  IO.println <|
    s!"Pending operations after two autoUpdates: {(current.operations readingListDb).size}, " ++
    s!"index operations: {(current.indexOperations readingListDb).size}"
  for idx in (current.tables["readingList"]?.map (·.indexes)).getD [] do
    IO.println s!"  read back: {repr idx}"
  -- `UPDATE ... RETURNING` and `DELETE ... RETURNING` name the mixed-case and the reserved columns
  -- on both sides of the statement.
  let moved ← HasModel.updateReturning (α := ReadingList)
    { value
        | .order => some (.int 99)
        | _ => none
      condition := .eq (.var ReadingListIndex.addedAt .int) (.int moby.addedAt) }
  IO.println s!"Updated: {moved.map fun r => (r.bookTitle.val, r.order)}"
  let dropped ← HasModel.deleteReturning (α := ReadingList)
    (.var ReadingListIndex.select .bool)
  IO.println s!"Deleted the selected row(s): {dropped.map (·.bookTitle.val)}"
  -- The index parser has to read a quoted column back out of a `CREATE INDEX` in either backend's
  -- spelling: SQLite stores the text as it was written, PostgreSQL re-prints it in its canonical
  -- form, with a cast. The parser is shared, so SQLite is where both are cheapest to check.
  let parsed : String → String := fun sql =>
    match SQL.Migration.parseCreateIndex? "i" sql with
    | some idx => ", ".intercalate (idx.keys.map fun k => s!"{k.column} {repr k.collation}")
    | none => "(unparsed)"
  IO.println <|
    s!"SQLite spelling `lower(\"title\")`: {parsed "CREATE INDEX i ON t (lower(\"title\"))"}"
  IO.println <|
    s!"PostgreSQL spelling `lower((\"title\")::text)`: " ++
    s!"{parsed "CREATE INDEX i ON t USING btree (lower((\"title\")::text))"}"
  -- A double quote inside a name is written twice inside the quotes, and has to be read back as
  -- one, or the name parsed out is not the name that was declared and the index never converges.
  IO.println <|
    s!"a doubled quote inside the name: {parsed "CREATE INDEX i ON t (\"a\"\"b\" ASC)"}"

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
  Sqlite.runDB ":memory:" indexDemo
  Sqlite.runDB ":memory:" conflictDemo
  Sqlite.runDB ":memory:" leftJoinDemo
  Sqlite.runDB ":memory:" (JoinExample.joinDemo "SQLite")
  Sqlite.runDB ":memory:" (RecursiveExample.recursiveDemo "SQLite")
  Sqlite.runDB ":memory:" extendDemo
  Sqlite.runDB ":memory:" correlateDemo
  Sqlite.runDB ":memory:" modelConflictDemo
  Sqlite.runDB ":memory:" (FloatExample.floatDemo "SQLite")
  Sqlite.runDB ":memory:" floatDefaultDemo
  Sqlite.runDB ":memory:" (KeyExample.keyDemo "SQLite")
  Sqlite.runDB ":memory:" saveWithoutKeyDemo
  Sqlite.runDB ":memory:" saveWithGeneratedKeyDemo
  Sqlite.runDB ":memory:" migrationsDemo
  Sqlite.runDB ":memory:" identifierDemo

end SqliteExample
