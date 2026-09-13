/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

/-!
# The example schema

The models the examples share, and the rows they start from. Backend-neutral on purpose: the
SQLite and PostgreSQL demos run the same schema, so it cannot live in either of them.
-/

namespace BookExample

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
  /-- The year of publication, unknown for some books. -/
  year : Option Int
  deriving Repr

/-- A tag, whose `id` the database assigns: `AutoKey` makes it a single-column auto-incrementing
primary key, which an insert leaves out. -/
@[model (dbName := "tag") mydb]
structure Tag where
  id : AutoKey
  label : VarChar 50
  deriving Repr

/-- A node of a tree — or of whatever the `parent` references actually form, which is the point:
the rows are walked by `Query.recursive`, and a cycle among them is something the walk has to
survive rather than something the schema rules out.

Part of the shared schema rather than of a schema of its own, because `autoUpdate` drops the tables
its target does not declare and the PostgreSQL demos share one database: a target naming only
`node` would take every other demo's tables with it. -/
@[model (dbName := "node") mydb]
structure Node where
  /-- An `AutoKey`, so that the table has the primary key a node table would have. The demo
  supplies the value anyway — a chain is easier to read with its ids written down than with ids
  the database chose. -/
  id : AutoKey
  /-- The node this one hangs under; absent for a root. -/
  parent : Option Int
  title : VarChar 100
  deriving Repr

/-- A measurement: a `Float` field, which becomes a `float` column, and an `Option Float`, which
becomes a nullable one.

Part of the shared schema for the same reason `node` is: `autoUpdate` drops the tables its target
does not declare, and the PostgreSQL demos share one database. -/
@[model (dbName := "sample") mydb]
structure Sample where
  id : AutoKey
  value : Float
  margin : Option Float
  deriving Repr

/-- A record keyed by an id its writer chooses rather than by one the database assigns: the key is
declared on the attribute, over a field of the structure. -/
@[model (dbName := "profile") (primaryKey := ["handle"]) mydb]
structure Profile where
  handle : String
  displayName : String
  visits : Int
  deriving Repr

/-- A composite key, in the order the two fields are named in. -/
@[model (dbName := "event") (primaryKey := ["session", "seq"]) mydb]
structure Event where
  session : String
  seq : Int
  body : String
  deriving Repr

/-- A model every column of which is part of its key, which leaves `HasModel.save` nothing to set:
the row that is already there is the row being written. -/
@[model (dbName := "membership") (primaryKey := ["groupName", "member"]) mydb]
structure Membership where
  groupName : String
  member : String
  deriving Repr

section KeyChecks

-- A field the key names has to be a column that can hold the key: an `Option` is a nullable
-- column, which PostgreSQL makes `NOT NULL` behind the declaration — leaving `autoUpdate` to
-- propose a `DROP NOT NULL` PostgreSQL then refuses, on every run — and which SQLite fills with
-- `NULL`s that do not conflict with each other, so two `save`s of `none` store two rows. Rejected
-- where the key is written, rather than in a schema neither backend keeps.
/--
error: the field `handle` of `BookExample.NullableKey` is an `Option`, so it is a nullable column, and its `primaryKey` names it. A primary key cannot be nullable: PostgreSQL makes such a column `NOT NULL` behind the declaration and then refuses the `DROP NOT NULL` `autoUpdate` proposes on every later run, and SQLite lets two rows carry `NULL` there, which is two rows under one key. Drop the `Option`, or key the model on another field.
-/
#guard_msgs in
@[model (dbName := "nullableKey") (primaryKey := ["handle"]) mydb]
structure NullableKey where
  handle : Option String
  body : String

end KeyChecks

section Identifiers

/-- A table that is nothing but awkward names: a mixed-case table name, a mixed-case column, and
two columns that are reserved words on both backends.

Every identifier the library emits is double-quoted, so `addedAt` stays `addedAt` rather than being
folded to `addedat` by PostgreSQL, and `order` and `select` are names rather than syntax errors.
Before the quoting, PostgreSQL introspection reported the folded name and `autoUpdate` proposed to
add `addedAt` again on every run. -/
@[model (dbName := "readingList") mydb]
structure ReadingList where
  /-- `ORDER` is a reserved word. -/
  order : Int
  /-- Mixed case, which is what PostgreSQL used to fold away. -/
  addedAt : Int
  /-- `SELECT` is a reserved word too. -/
  «select» : Bool
  /-- Character data, so that a case-insensitive index has something to be declared over. -/
  bookTitle : VarChar 200
  deriving Repr

/-- The schema with two indexes over mixed-case columns, one of them case-insensitive. That is the
round trip the quoting has to survive twice over: the index is declared as `lower("bookTitle")` and
read back in whatever spelling the backend hands its definition out in.

The whole of `mydb` rather than a database of its own: `autoUpdate` migrates a database to a target
schema, so a target naming only this table would drop the tables of every other demo. The
PostgreSQL demos share one database, and run in sequence. -/
def readingListDb : DatabaseRecipe :=
  (%database mydb).recipe.withIndexes "readingList" <| tableIndexes ReadingListIndex
    [{ name := "idx_readingList_addedAt", keys := [{ column := .addedAt, direction := .desc }] },
     { name := "idx_readingList_bookTitle",
       keys := [{ column := .bookTitle, collation := .caseInsensitive }] }]

def gatsby : ReadingList where
  order := 1
  addedAt := 20260101
  «select» := true
  bookTitle := v"The Great Gatsby"

def moby : ReadingList where
  order := 2
  addedAt := 20260202
  «select» := false
  bookTitle := v"Moby-Dick"

end Identifiers

/-- The connection string the PostgreSQL examples use: `DB_POSTGRES_URL` if it is set, so that the
suite can be pointed at another server or database, and the local test database otherwise. -/
def postgresUrl : IO String := do
  return (← IO.getEnv "DB_POSTGRES_URL").getD "postgresql://testuser:secret@localhost/testdb2"

/-- Print a statement's SQL and check that it contains no subquery.

The shape of the SQL is the substance of the join demos, and a reader of a printed statement does
not necessarily notice a subquery that crept back into it, so the demo asserts it rather than only
showing it. The two spellings are the two the renderer can produce: `( SELECT` for a subquery in a
`FROM`, `(SELECT` for one used as a value. -/
def printFlatSql (label : String) (sql : String) : IO Unit := do
  IO.println s!"{label}: {sql}"
  if (sql.splitOn "( SELECT").length != 1 || (sql.splitOn "(SELECT").length != 1 then
    throw <| IO.userError s!"the SQL for `{label}` was expected to be flat, but nests a subquery"

/-- Print a statement's SQL and check that the subquery in it carries an alias, which PostgreSQL 15
and older require of any subquery in a `FROM`. -/
def printAliasedSql (label : String) (sql : String) : IO Unit := do
  IO.println s!"{label}: {sql}"
  if (sql.splitOn ") AS \"t").length == 1 then
    throw <| IO.userError s!"the subquery in `{label}` has no alias"

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
  year := some 1998

def drama : Book where
  title := v"A drama"
  author := lisa.name
  year := none

section DSLChecks

open Db.Query.DSL

/-- A term over a binder of the enclosing definition is a constant of the query, and is embedded as
a literal. -/
def booksBy (name : VarChar 100) : QuerySet Book := query% do
  let b ← from Book
  guard b.author = name
  select b

-- A term the DSL cannot translate has to be reported as such, even when it has the type of a
-- database value: embedding it would let a row variable escape the query block.
/--
error: unsupported expression in query condition: `a.age + 1`
-/
#guard_msgs in
-- An `example`, not a `def`: the failed elaboration leaves a `sorry` behind, which as a compiled
-- top-level constant would abort the executable at load time.
example : QuerySet Author := query% do
  let a ← from Author
  guard a.age + 1 > (5 : Int)
  select a

-- `nocase` is `lower(...)`, so it needs a character column. SQLite would quietly sort the text a
-- number folds to and PostgreSQL has no `lower(integer)` at all, so the elaborator rejects it.
/--
error: `nocase` orders by `lower(...)`, which needs character data, but `a.age` has type `DBType.int`
-/
#guard_msgs in
example : QuerySet Author := query% do
  let a ← from Author
  select a
  order_by a.age nocase

end DSLChecks

end BookExample
