# A backend independent database client in Lean

This repository contains a relational database client library in Lean. The high-level interface
is backend and SQL independent. To give a brief impression, the following is an example:

```lean4
import Db
-- The example ends on a PostgreSQL connection, and the PostgreSQL backend is not part of `Db`;
-- see "The PostgreSQL backend" below for the import and the Lake option it needs.
import Db.Postgres

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

`import Db` gives the query language, the model layer, the migrations and the **SQLite** backend.
SQLite is included because `leansqlite` vendors the database itself, so it costs a dependent package
nothing but the build.

That snippet is the whole configuration a SQLite-only package needs. It builds and runs with nothing
on the machine but a C compiler: no PostgreSQL headers, no `pg_config`, no libpq. The PostgreSQL FFI
shim is not compiled and nothing links against libpq unless you ask for it below.

### The PostgreSQL backend

PostgreSQL is an FFI binding against libpq, so it is behind `import Db.Postgres` rather than in the
root module, and behind the `postgres` Lake configuration option as well. The import alone is not
enough: Lake links the external libraries of every package that owns an imported module into every
executable built from it, and builds them first, so an unconditional `extern_lib` here would make
*your* SQLite-only package compile the shim — and need `libpq-fe.h` — whether or not it ever opened
a PostgreSQL connection. Only a target that is absent from the configuration is truly not built, and
the option is what removes it.

So a package that uses the backend turns the option on in its `[[require]]`, and names libpq in its
own link arguments:

```toml
[[require]]
name = "Db"
git = "https://github.com/chrisflav/db"
rev = "master"
options = {postgres = "on"}

[[lean_exe]]
name = "myapp"
root = "Main"
# The absolute path, not `-L/usr/lib/... -lpq`: the toolchain ships its own C runtime, and putting
# the system library directory on the linker's search path makes it resolve glibc there too. Ask
# `pg_config --libdir` where libpq is on the machine you are building on.
moreLinkArgs = ["/usr/lib/x86_64-linux-gnu/libpq.so"]
```

In a `lakefile.lean` the same two pieces are

```lean
require db from git "https://github.com/chrisflav/db" @ "master"
  with NameMap.empty.insert `postgres "on"

lean_exe myapp where
  root := `Main
  moreLinkArgs := #["/usr/lib/x86_64-linux-gnu/libpq.so"]
```

The link arguments are yours to supply because Lake does not propagate a dependency's link arguments
to the packages that depend on it — only the FFI object itself, which then has nothing to resolve
its `PQ*` calls against. `lakefile.lean` here discovers the path with `pg_config`, in
`libpqLinkArgs`, which is worth copying if you build on more than one platform.

`import Db.Postgres` type-checks with the option off, since a `.olean` of `@[extern]` declarations
needs no object behind them; it is linking an executable that calls them which needs the shim.

### Building this repository

The SQLite half of the example suite is the test driver and needs nothing special:

```sh
lake build testdb && lake exe testdb      # or: lake test
```

The PostgreSQL half needs the option, and needs it *before* the target name for `lake exe`, which
passes everything after the target to the program:

```sh
lake -R build testdb-postgres -Kpostgres=on
lake exe -Kpostgres=on testdb-postgres
```

It talks to the server named by `DB_POSTGRES_URL`, defaulting to
`postgresql://testuser:secret@localhost/testdb2`. `lake -R` is what re-reads the configuration after
a lakefile or option change; without it Lake reuses the configuration it cached for the previous
setting of `-Kpostgres`.

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
| `b.note = "classic"` | `= 'classic'` (a `String` constant is a `text` literal, `DBExpr.text`) |
| `s.value > 1.0` | `> 1.0` (a `Float` constant is a `float` literal, `DBExpr.float`) |
| `like b.title "A drama%"` | `LIKE 'A drama%'`, with `\\` escaping the next character |
| `contains b.title "100%"` | `LIKE '%100\\%%'`, with the wildcards in the needle escaped |
| `isIn a.name [v"Mike", v"Nora"]` | `IN ('Mike', 'Nora')` |

`like`, `contains` and `isIn` live in the `Db.Query.DSL` namespace and are only meaningful inside a
query block. In a `like` pattern `%` and `_` are wildcards and `\` escapes the character after it,
including itself, so a literal backslash is written `\\`; this is declared to the backend as
`ESCAPE '\'`, since PostgreSQL and SQLite disagree on the default. `contains` does that escaping
for you. Both take a character-data column, either a `varchar n` one (a `VarChar n` field) or a
`text` one (a `String` field). A nullable column projects to an `Option`-valued field, so `some` is
written around a literal it is compared with; testing for `NULL` is `isNone`, not `= none`.

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

Joins nest, in either direction: `(a × b) × c` and `a × (b × c)` are both cross products of three
tables, and their columns are named accordingly (`left__left__title`, `right__right__order`). A
`leftJoin` over a join is a join too. Filtering the *right-hand side* of a left join is not the
same as filtering the join — `a ⟕ σ_p(b)` keeps the left rows that `p` rejects, with `NULL`s —
and the translation says so by putting that filter into the `ON` rather than into the `WHERE`. A
right-hand side that *computes* a column, with `extend` or `correlate`, becomes a subquery instead:
a left row that matches nothing has to come back with `NULL` in that column too, and an expression
in the join's own `SELECT` list would be evaluated per row of the join and hand it a value.

All of this comes out as one flat statement: see [Design](#design) below.

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

A key may say how it compares and where it puts its `NULL`s:

```lean
query% do
  let b ← from Book
  select b
  order_by b.title nocase
  order_by b.year nulls_last
```

`nocase` folds case, and `nulls_first`/`nulls_last` place the nulls — worth saying explicitly,
since both backends sort `NULL`s first ascending and last descending, so a query that wants them
consistently at one end has to ask. On a `SortKey` these are the `collation` and `nulls` fields.

`nocase` is emitted as `lower(...)` rather than as a declared collation: SQLite's `NOCASE` and
PostgreSQL's collations have nothing in common, `lower` is in both and folds ASCII the way `NOCASE`
does, and being an ordinary expression it is something both can build an index on — which is what
lets an index declared `caseInsensitive` serve an `ORDER BY ... nocase`.

`HasModel.count` counts the rows a query set matches without fetching them:

```lean4
IO.println s!"{← HasModel.count (QuerySet.all (α := Book))} books"
```

More general aggregation is `Query.aggregate`, which takes an `Aggregation source out`: every
column of the output view `out` is either a column of `source` that is grouped over, or an
aggregate (`COUNT(*)`, `COUNT`, `COUNT DISTINCT`, `SUM`, `AVG`, `MIN`, `MAX`) of the rows of a
group. A function is only applicable to the types it is defined on, so `SUM` over a `varchar`
column does not elaborate. Supplying the output view is what keeps this general — it names and types the
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

`SUM` and `AVG` are the two that need a number. `SUM` gives a value of the column's own type;
`AVG` gives a `float` whatever it is taken of, an average being a value an integer column has no
room for and not a value either backend hands back as one. Both are `NULL` for a group whose
values are all `NULL`, as `MIN` and `MAX` are, and the output view has to say so.

`Query.extend` adds a column computed from the row it belongs to, which is what a `SELECT` list
does beyond naming columns — `project` renames and drops them and `aggregate` computes over a
group, but neither computes a value from the row in front of it:

```lean
let inTenYears : Query mydb _ :=
  .extend "age_in_10" { type := .int, nullable := false }
    (.add (.var AuthorIndex.age .int) (.int 10))
    (.all (HasModel.model Author).index)
```

`DBExpr` has `add`, `sub` and `mul`, on integers only. Arithmetic on `float` columns is not there
yet; what a float column can do in an expression is be compared with another one and with a
literal.

`Query.correlate` computes one such aggregate per row of an outer query, over the rows of a
subquery correlated with that row — the `(SELECT COUNT(*) FROM child WHERE child.parent =
parent.id)` of a `SELECT` list:

```lean
let counted : Query mydb _ :=
  .correlate "books"
    (.all (HasModel.model Author).index)   -- the outer rows
    (.all (HasModel.model Book).index)     -- the rows to aggregate
    (.eq (.var (Sum.inr BookIndex.author) (.varchar 100))
         (.var (Sum.inl AuthorIndex.name) (.varchar 100)))
    .countAll
```

None of the other constructors express this. A join multiplies the outer rows by the inner ones
rather than reducing them, and an aggregate over a join loses the outer rows that match nothing —
where this keeps the author who wrote no books, with a count of `0`.

The result view is the outer one extended by a single column under the given name, whose type and
nullability are the aggregate's: `countAll` gives a non-null `int`, while `MIN`/`MAX`/`SUM` are
nullable, being `NULL` for a row the subquery matches nothing for. The condition is written over
`outer.prod inner`, so `Sum.inl` names an outer column and `Sum.inr` an inner one. A `group` entry
is rejected, a subquery returning one row per group not being a value a `SELECT` list has room
for.

## Recursive queries

`Query.recursive` is SQL's `WITH RECURSIVE`: the rows of a base query, then repeatedly the rows of
a step computed over the rows found so far, until a step finds nothing new. The step reaches those
rows through `Query.cteRef`, which names the relation being defined:

```lean
| cteRef (name : String) (view : View d) : Query d view
| recursive {view : View d} (name : String) (base : Query d view) (step : Query d view) :
    Query d view
```

`base` and `step` produce the same view — the common table expression has one column list, and the
`UNION ALL` joining the two matches its operands by position. Nothing in the types ties a `cteRef`
to its `recursive`: `Query` is an inductive and cannot bind a variable, so the reference is by
name, and a `cteRef` outside its `recursive` renders SQL naming a relation that does not exist.

The worked example is an ancestor walk on a table that references itself, `node(id, parent, title)`.
The walk carries a `depth` column, so the view it produces is a `node` row next to that:

```lean
abbrev depthColumn : Column := { type := .int, nullable := false }

abbrev ancestorView : View mydb :=
  (Table.view nodeIndex).prod (View.singleton mydb "depth" depthColumn)

-- The step: for every row found so far, the node its `parent` names, one step deeper.
def ancestorStep (bound : Int) : Query mydb ancestorView :=
  .project
    (View.Hom.ofMap fun i =>
      match i with
      | Sum.inl col => Sum.inl (Sum.inr col)
      | Sum.inr d => Sum.inr d)
    (.filter
      (.and
        (.eq (.var (Sum.inl (Sum.inr NodeIndex.id)) .int)
             (.var (Sum.inl (Sum.inl (Sum.inl NodeIndex.parent))) .int))
        (.lt (.var (Sum.inl (Sum.inl (Sum.inr ⟨⟩))) .int) (.int bound)))
      (.extend "depth" depthColumn
        (.add (.var (Sum.inl (Sum.inr ⟨⟩)) .int) (.int 1))
        (.join (.cteRef "ancestors" ancestorView) (.all nodeIndex))))

def ancestorsOf (start : Int) (bound : Int := 64) : Query mydb ancestorView :=
  .recursive "ancestors"
    -- The base: the row to start from, at depth 0.
    (.extend "depth" depthColumn (.int 0)
      (.filter (.eq (.var NodeIndex.id .int) (.int start)) (.all nodeIndex)))
    (ancestorStep bound)
```

The step joins the rows found so far with the whole table, so it is written over
`(node × depth) × node`: `Sum.inl (Sum.inl _)` is a column of a row found so far,
`Sum.inl (Sum.inr ⟨⟩)` is that row's depth, and `Sum.inr _` is a column of the candidate parent.
The `extend` puts the new depth beside all of it and the `project` brings the result back onto
`ancestorView`, which is the view `base` and `step` have to agree on. `View.Hom.ofMap` is the
projection's map with its naming obligation discharged by splitting the index into cases and
checking each by `rfl`; an index that needs more than one split takes the proof explicitly, as in
`View.Hom.ofMap f (by rintro ((_ | _) | _) <;> rfl)`.

Sorted by depth and run, that walk generates (reformatted here; it is emitted on one line):

```sql
WITH RECURSIVE "ancestors" AS (
  SELECT "t1"."id" as "left__id", "t1"."parent" as "left__parent",
         "t1"."title" as "left__title", 0 as "right__depth"
    FROM "node" AS "t1" WHERE ("t1"."id") = (4)
  UNION ALL
  SELECT "t3"."id" as "left__id", "t3"."parent" as "left__parent",
         "t3"."title" as "left__title", ("t2"."right__depth") + (1) as "right__depth"
    FROM "ancestors" AS "t2" CROSS JOIN "node" AS "t3"
   WHERE (("t3"."id") = ("t2"."left__parent")) AND (("t2"."right__depth") < (64)))
SELECT "t4"."left__id" as "left__id", "t4"."left__parent" as "left__parent",
       "t4"."left__title" as "left__title", "t4"."right__depth" as "right__depth"
  FROM "ancestors" AS "t4" WHERE true ORDER BY "t4"."right__depth" ASC
```

The `WITH` belongs to the statement, not to the query that needed it: whatever is built around a
`recursive` — an `ORDER BY`, a join, a filter — hoists the declaration to the top, which is the
only place SQL accepts it. Nested statements never render a `WITH` of their own, and a top-level
one is visible inside all of them.

Three restrictions come with this:

- **The step may name the CTE exactly once, and not inside a subquery.** That is SQLite's rule; it
  rejects the other shape with `circular reference: ancestors`. A step built out of
  `join`/`filter`/`extend`/`project`, like the one above, satisfies it, because those translate to
  one flat `SELECT`. A step that orders or limits its rows does not: those clauses belong to the
  `UNION ALL` and not to one of its branches, so the step becomes a subquery around the
  self-reference. Nor will either backend run a step that aggregates — SQLite calls it a
  `recursive aggregate query`, PostgreSQL says aggregate functions are not allowed in a recursive
  query's recursive term. A `base` that orders or limits is fine: it becomes a subquery too, and
  there is no self-reference in it to object to.
- **The column types of `base` and `step` must agree per position.** PostgreSQL takes the type of
  every column of the CTE from the non-recursive term and insists the other branch agree. An `int`
  literal `0` against `depth + 1` is fine. A `DBExpr.str` against a `varchar(n)` column is not, in
  either direction: the literal is emitted as a bare `'...'`, which PostgreSQL types as `text`, and
  it reports `recursive query "ancestors" column 3 has type text in non-recursive term but type
  character varying overall`. There is no cast to write it with, so take the value from a column of
  the right type on both sides — which is what the walk above does with `title`. SQLite, which does
  not type a column this way, runs it either way.
- **`UNION ALL`, so a cycle has to be cut by the step.** A row reached twice is returned twice, and
  a cycle among the `parent` references would be walked forever; the `depth < bound` conjunct above
  is what stops it. Started inside a two-node cycle, the query above returns 65 rows — the starting
  row and 64 steps — rather than not returning.

Two `recursive` queries with the same name in one statement declare the same CTE twice and the
database rejects the statement; names have to be unique per statement. They are not renamed for
you, the name being what a reader of the generated SQL sees.

## Column types and defaults

`DBType` covers `bool`, `int`, `varchar n`, unbounded `text` and `float`. A model field of type
`String` becomes a `text` column, one of type `Float` a `float` column, and `Option α` a nullable
one. A comparison has both operands at one `DBType`, so a `text` column is compared with — and
updated to — `DBExpr.text`, a `varchar n` one `DBExpr.str`, and a `float` one `DBExpr.float`.

### Floating point

`float` is a `Float`: an IEEE 754 double, the only floating-point type Lean has. It is declared as
`double precision`, which is PostgreSQL's own name for it and the name PostgreSQL reports back,
while SQLite — which takes any type name and derives an affinity from it — gives anything
containing `DOUB` the same `REAL` affinity the word `REAL` has, and reports the declared text
verbatim. So one spelling serves both dialects and `autoUpdate` reaches a fixed point on either.

What a floating-point column costs is precision on the way in and on the way out, and both ends
here are written so that a value read back is the value that was written, bit for bit.

Writing is the literal. `Float.toString` prints six digits after the point — `toString (1e-7 :
Float)` is `"0.000000"`, and every subnormal is zero — and `Lean.toJson` goes through the same
printer, so neither can be what a literal is built from. `Float.toDecimalString` prints seventeen
significant digits of the *exact* binary value instead, which is the shortest precision at which
every double round-trips: `Float.frExp` gives the mantissa and exponent, `m · 2^53` is an integer,
and the decimal digits are a long division carried out in exact `Nat` arithmetic. There is always
a digit on either side of the point (`4.0`, never `4`), so that nothing a float column is set to
reads as an integer.

NaN and the infinities have no literal in either dialect — SQLite has none at all, and
PostgreSQL's `'NaN'::double precision` is a cast of a string rather than a number. Rendering one is
therefore a panic, not a fallback: it names the value on stderr and leaves behind SQL the database
refuses, rather than quietly storing something else.

Reading is the backends' own printing, and neither prints enough by default. SQLite converts a
`REAL` to text at fifteen significant digits, so `0.30000000000000004` would come back as `0.3` and
the largest double as an infinity; the SQLite backend therefore reads a value SQLite holds as a
float through `sqlite3_column_double` and prints it with the printer above. Which values those are
is decided by the value's own runtime type rather than by the declared column type, SQLite storing
what it was given whatever the column says. PostgreSQL prints what `extra_float_digits` asks for,
which since version 12 defaults to the shortest text that round-trips but on older servers is
fifteen digits, so the connection sets it to the maximum on open. `Float.ofDecimalString?` reads
back what either prints — `0.1`, `-3`, `1e-07`, `1.0e+20`, `1E5`, `.5` — and the spellings
`Infinity` and `NaN` besides, so that a row holding one is reported rather than refused.

`ColumnDefault` has no floating-point literal: it derives `DecidableEq` and `Hashable`, and `Float`
has neither. A default on a float column is written as an expression instead, `.call "0.0"`, which
is also what makes it converge — two expression defaults compare equal however the database
rewrites the text of one, where a literal would have to survive the rewriting.

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

A model's key is declared on the attribute, as the field names it is made of, in the order it is
made of them:

```lean4
@[model (dbName := "profile") (primaryKey := ["handle"]) mydb]
structure Profile where
  handle : String
  displayName : String

@[model (dbName := "event") (primaryKey := ["session", "seq"]) mydb]
structure Event where
  session : String
  seq : Int
  body : String
```

The names are checked against the structure: one that is not a field, or one named twice, is an
error where the attribute is written rather than SQL naming a column that is not there. Without
this a model had no key at all unless it had an `AutoKey` field, and `insertIfAbsent` and `upsert`
then had nothing to conflict on — a record keyed by an id its writer chooses, which is most of
what a record store holds, could not say so.

A column may be `autoIncrement`, meaning the database assigns its value; `Database.Insert.ofEntry`
leaves such a column out, so the model layer never sends one. In a model structure a field of type
`AutoKey` becomes exactly that — an auto-incrementing single-column primary key:

```lean4
@[model (dbName := "tag") mydb]
structure Tag where
  id : AutoKey
  label : VarChar 50
```

A generated key and a declared one exclude each other, and the attribute says so rather than
emitting a schema neither backend would create: the database assigning a column's value only means
anything if that column *is* the key, so a `primaryKey` beside an `AutoKey` field is an error.

`CREATE TABLE` renders these per dialect, since the two backends spell a generated key differently
(`INTEGER PRIMARY KEY AUTOINCREMENT` against `GENERATED BY DEFAULT AS IDENTITY`), and both backends
read all of it back so that `autoUpdate` reaches a fixed point. SQLite only generates the value of
a column that is exactly its `INTEGER PRIMARY KEY`, so a schema whose generated column is not its
whole primary key is refused there rather than created with a key nobody declared. Table creations
are ordered so that a table comes after the tables its foreign keys reference, and drops in the
reverse.

## Indexes

A `Table` declares indexes beside its constraints. Each has a name — which is what `DROP INDEX`
takes, and which both backends require to be unique across the whole database — and a list of keys,
each with the same direction and collation a `SortKey` has, so that an index can be declared to
match the `ORDER BY` it is meant to serve:

```lean
def noteTable : Table where
  Index := NoteIndex
  columns := ...
  indexes :=
    [{ name := "idx_note_state", keys := [{ column := .state }] },
     { name := "idx_note_title", keys := [{ column := .title, collation := .caseInsensitive },
                                          { column := .id }] },
     { name := "idx_note_tag", keys := [{ column := .tag }], unique := true }]
```

Unlike a constraint change, an index change **is** migrated: `CREATE INDEX` and `DROP INDEX` say
the whole of it, where a constraint change would mean rebuilding the table. `autoUpdate` creates a
declared index that is missing, and drops and re-creates one whose keys or uniqueness changed,
neither backend being able to alter an index in place.

It manages only the index *names* the target declares. An index the database has under a name the
schema does not mention is left alone: `autoUpdate` is not the only thing that may have created an
index, and dropping one it did not put there is not a migration.

`@[model]` generates a table with no indexes, because which of a structure's fields are worth an
index is not something the structure says. Declare them against the recipe, naming the columns
through the generated index type:

```lean
def indexedDb : DatabaseRecipe :=
  (%database mydb).recipe.withIndexes "book" <| tableIndexes BookIndex
    [{ name := "idx_book_author", keys := [{ column := .author }] }]

autoUpdate indexedDb
```

Both backends read their indexes back by parsing the `CREATE INDEX` text they store, since neither
reports the keys in a structured form that an expression key survives. PostgreSQL hands the
definition back in its own spelling rather than the one it was given — a `lower(title)` on a
`varchar` column comes back as `lower((title)::text)` — which is normalised on the way in, so that
`autoUpdate` reaches a fixed point on both.

The operation language describes column changes only, so a **constraint change on an existing
table is not migrated**. Rather than applying such a migration as a silent no-op, `autoUpdate`
aborts and names the tables whose constraints differ; migrate those by hand, or drop and recreate
them. A declared migration can carry such a change as a raw `Step.sql` step — see below.

## Migrations

`autoUpdate` looks at the database in front of it and works out what to do. That is what you want
in development and not what you want in production: what it does depends on the database it happens
to find, so two deployments of the same code can end up with different schemas; it carries no data
migrations; and it refuses a constraint change outright. A **migration** is the other way round —
a named, ordered list of steps, written in Lean and committed with the code, so that the schema is
a function of the code alone.

```lean
import Db

open Db.Migration

def migration0001 : Migration where
  name := "0001_initial"
  steps :=
    [ .createTable "author"
        { columns := .ofList
            [("name", { type := .varchar 100, nullable := false }),
             ("age", { type := .int, nullable := false })]
          primaryKey := ["name"] },
      .createIndex "author" { name := "idx_author_age", keys := [{ column := "age" }] } ]

def migration0002 : Migration where
  name := "0002_retired"
  steps :=
    [ -- A schema step, in the operation language `autoUpdate` uses.
      .addColumn "author" "retired" { type := .bool, nullable := false,
                                      default? := some (.bool false) },
      -- A data step: ordinary typed code, polymorphic in the monad, so it runs on either backend.
      .run do
        let _ ← HasModel.update (α := Author)
          { value | .retired => some .true | _ => none
            condition := .gt (.var AuthorIndex.age .int) (.int 70) },
      -- A raw statement, for what the operation language does not say.
      .sql "UPDATE author SET retired = false WHERE name = 'Nobody'",
      .dropIndex "author" "idx_author_age" ]

def migrations : List Migration := [migration0001, migration0002]
```

The step constructors are `createTable`, `dropTable`, `renameTable`, `addColumn`, `dropColumn`,
`renameColumn`, `alterColumn`, `createIndex`, `dropIndex`, `sql`, `sqlByDialect` and `run`. A
`createTable` takes a `TableRecipe` and ignores its `indexes`, `CREATE TABLE` creating none; declare
those as `createIndex` steps. A `run` step is a `{m : Type → Type} → [Monad m] →
[DBMonadWithMigrations m] → m Unit`, which is everything `DBMonad.lookup`/`insert` and the
`HasModel` functions need, and nothing a backend does not provide — which is what lets one migration
be declared once and applied on both.

`migrate` applies the migrations the database has not recorded, in list order, and records each:

```lean
let applied ← Db.Migration.migrate migrations now   -- `now`: Unix seconds
```

The record lives in a table `db_migrations (name text NOT NULL PRIMARY KEY, applied_at integer NOT
NULL)`, which `migrate` creates with a single `CREATE TABLE IF NOT EXISTS` — one statement, so that
two `migrate`s starting at the same time cannot both find it absent and both create it. It is read
and written through the ordinary typed API, so it works on every backend without a line of
backend-specific SQL. `now` is a parameter rather than a clock call, so that the class need not be
over `IO` and a test can pin the time; the CLI below supplies it from `Std.Time.Timestamp.now`.

`migrate` validates before it applies anything: the names have to be unique, and every name the
database records has to appear in the list. A recorded migration the code does not declare means the
database is ahead of the code, and applying the rest on top of a history nobody has is how a schema
ends up in a state no code describes. `Db.Migration.applied` lists what is recorded and
`Db.Migration.pending` what is not (by name — `Migration` is in `Type 1`, a `run` step quantifying
over the monad, so it cannot be returned from `m`). Neither of them creates anything: a database
with no tracking table has applied no migrations, which is what they report.

`db_migrations` is a table like any other and schema introspection reports it, so `autoUpdate` would
drop it as a table the target does not declare. It does not: `autoUpdate` hides the framework's own
tables from the schema it diffs, so the two can be used in the same database — `autoUpdate` while
developing, migrations once the schema is deployed.

### `atomic`, and the SQLite rule

A migration is applied inside a transaction by default, so a step that fails leaves neither a
half-applied schema nor a record claiming the migration was applied.

Its record is written *first*, inside that transaction, which is what keeps two `migrate`s running
at the same time from applying the same migration twice: `name` is the primary key of the tracking
table, so the second run's insert blocks on the first run's uncommitted row and then fails on the
duplicate key, before it has applied a single step, and its transaction takes the attempt back with
it. A migration declared `atomic := false` writes its record after its last step instead — it has no
transaction to be taken back, so a record written first would outlive a failure half way.

SQLite cannot change the type or nullability of a column in place; the backend realises such a
change by rebuilding the table, and the rebuild has to turn off foreign-key enforcement while it
drops the old table. `PRAGMA foreign_keys` is a no-op inside a transaction — and inside a savepoint,
which is the same transaction as far as it is concerned — so the enforcement would stay on and the
`DROP TABLE` would perform an implicit `DELETE` that fires the `ON DELETE` actions of every table
referencing this one. The backend therefore refuses to rebuild inside a transaction, before it has
done anything, and says so.

The same rebuild is how SQLite realises an `ADD COLUMN` it rejects outright: a `NOT NULL` column
whose default is missing or `NULL`, or a column with a non-constant default. That matters because
`ADD COLUMN` of a `NOT NULL` column is exactly what `makemigrations` writes for a new non-optional
field of a model, so the rule is not only about `alterColumn`. `render` puts its comment above any
plan containing either kind of step.

A migration containing such a step that is to be applied to SQLite declares

```lean
  atomic := false
```

and is then applied step by step, its record written after the last one. PostgreSQL has no such
restriction and runs the same migration atomically.

### `makemigrations`

`planSteps migrations target` computes the steps that take the schema the migrations fold to over to
`target`, the schema the code declares — typically `(%database mydb).recipe`, possibly
`.withIndexes …`. An empty plan means there is nothing to write. `render name steps` prints the
plan as the source of a complete Lean module:

```lean
import Db

/-- Generated by `makemigrations`; edit freely. -/
def migration_0003_pages : Db.Migration.Migration where
  name := "0003_pages"
  steps := [
    .addColumn "book" "pages" { type := .int, nullable := true },
    .dropIndex "book" "idx_book_year"
  ]
```

What it cannot generate: a **constraint change** on an existing table, which the operation language
has no word for — `planSteps` reports the tables whose constraints differ instead of emitting
something that looks like a migration and does nothing; write that step by hand as a `Step.sql`.
And it cannot see into a `sql` or `run` step: those are taken to leave the schema exactly as the
schema steps around them describe, so a raw statement that changes the schema has to be accompanied
by the schema step that says so.

Unlike `autoUpdate`, an index the declared schema no longer names **is dropped**. `autoUpdate` runs
against a live database that may hold indexes nobody declared and leaves those alone; here both
sides are Lean code, so an index that disappeared from the code is a deletion like any other. Every
drop is planned before every create, because an index name is unique across the whole database on
both backends: an index name that moves from one table to another has to be freed before it is
taken again.

Dropping a column takes the indexes over it with it. The plan says so explicitly, emitting the
`dropIndex` steps before the `dropColumn`: PostgreSQL would drop such an index along with the
column, but SQLite refuses to drop an indexed column at all, and the pair in that order is what both
backends accept. A **constraint** over the column is the other case: dropping a column that is part
of the primary key, of a `UNIQUE` group or of a foreign key is refused, with the same reasoning as
for any other constraint change — it is never migrated silently. Drop the constraint by hand in a
`Step.sql` step first, or drop and recreate the table.

A plan containing an `alterColumn` is rendered with a comment saying that it rebuilds the table on
SQLite and may need `atomic := false`. The generator leaves `atomic` at its default rather than
deciding: whether the rule applies depends on the backend the migration will be applied to, which is
not something the declared schema says.

### The command line

`Db.Migration.Cli.main` is the four commands every project wants, over the four things every project
has to supply:

```lean
-- Migrate.lean
import Db

def config : Db.Migration.Cli.Config Sqlite.M where
  migrations := MyApp.migrations
  target := (%database mydb).recipe
  directory := "MyApp" / "Migrations"
  run x := Sqlite.runDB "app.db" x

def main (args : List String) : IO UInt32 :=
  Db.Migration.Cli.main config args
```

| command | what it does |
| --- | --- |
| `migrate` | applies the migrations the database has not recorded, printing each |
| `showmigrations` | `[X] name` for the recorded ones, `[ ] name` for the rest |
| `makemigrations <desc>` | writes `<directory>/NNNN_<desc>.lean` and says to add it to the list |
| `check` | exits 1 and lists the missing steps when the declaration is ahead, for CI |

`migrate` prints `Nothing to migrate.` when there is nothing to do, and `makemigrations` and
`check` print `No changes detected.` when the plan is empty. An unknown command prints the usage
and exits 2. `NNNN` is one more than the highest leading number
among the names the migration list already has, zero-padded to four digits, which is what makes the
names sort in the order they were created.

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

An insert can say what to do with a row it cannot store because storing it would violate a
uniqueness constraint — a primary key, a `UNIQUE` group, or a unique index:

```lean4
/-- A label, keyed by its name rather than by a generated id. -/
@[model (dbName := "label") mydb]
structure Label where
  name : VarChar 50
  colour : VarChar 20

/-- `name` is unique, declared as a unique index on the recipe — see Indexes above. -/
def labelDb : DatabaseRecipe :=
  (%database mydb).recipe.withIndexes "label" <| tableIndexes LabelIndex
    [{ name := "idx_label_name", keys := [{ column := .name }], unique := true }]

-- Skip the row if one conflicting with it is already there. Returns whether it was inserted.
let stored ← HasModel.insertIfAbsent ({ name := v"urgent", colour := v"red" } : Label)

-- Or overwrite: on a conflict on `name`, set `colour` to the value this insert carried.
let rows ← HasModel.upsert ({ name := v"urgent", colour := v"blue" } : Label)
  [LabelIndex.name] [LabelIndex.colour]
```

The conflict has to be one the row can actually have. A column whose value the database generates
— an `AutoKey`, say — is left out of the statement so that the database can assign it, which also
means no row ever conflicts on it: `insertIfAbsent` on a model whose only key is an `AutoKey`
stores its row every time and always returns `true`. `target` and `set` have the model's index
type, which a bare `.name` cannot be resolved against, so they are written out in full.

On a `Database.Insert` this is the `onConflict` field, `.error` (the default), `.ignore`, or
`.update target set`. It is emitted as `ON CONFLICT ... DO NOTHING`/`DO UPDATE`, which both
backends have — SQLite since 3.24, so its own `INSERT OR IGNORE` is not needed and one spelling
serves both. `DO UPDATE` needs a conflict target on both: neither will guess which constraint an
update is meant to resolve.

One exception: an insert that supplies no column at all has to be written `INSERT INTO t DEFAULT
VALUES`, and SQLite lets no `ON CONFLICT` follow that. `.ignore` is therefore rendered as
`INSERT OR IGNORE INTO t DEFAULT VALUES` there, which for a row that carries no value of its own
means the same thing; `.update` has no spelling at all in that position, and the SQLite backend
reports it rather than emitting SQL the database would reject. Supply at least one column if you
need to upsert.

A skipped row is a row the statement did not store, so `insertReturning` on an `.ignore` insert
returns no rows rather than the row that was already there.

`HasModel.save` is the upsert a record store writes with: store this row, replacing whatever is
under its primary key.

```lean4
HasModel.save ({ handle := "ada", displayName := "Ada Lovelace" } : Profile)
```

It is `upsert x` on the table's primary key, setting every column that is not part of that key, so
it needs a key to conflict on: a model that declares none aborts, naming the table, rather than
storing a second row that looks like the first. A model every column of which is part of its key
has nothing to set, and there `save` is an `insertIfAbsent` — the row already there *is* the row
being written. A key the *database* assigns is not one to save on either: an `AutoKey` is left out
of the statement, so nothing conflicts on it and `insert`/`insertReturning` is what writes such a
row.

`DBMonadTransactional.withTransaction` groups several operations into one atomic unit, committing
if the block succeeds and rolling back if it fails. A nested call is a savepoint, so its failure
discards only its own work while an outer failure still discards everything. On PostgreSQL only a
failure of the backend's own exception type rolls back; an `IO` error thrown underneath escapes
with the transaction still open.

## Identifiers

Every table, column, index and alias name the library emits is double-quoted, so names keep the
case they were declared with on both backends and may be reserved words:

```lean4
@[model (dbName := "readingList") mydb]
structure ReadingList where
  order : Int
  addedAt : Int
  «select» : Bool
```

`addedAt` is stored as `addedAt`, not as `addedat`, and `order` and `select` are names rather than
syntax errors. Without the quoting PostgreSQL folds an unquoted identifier to lower case while
SQLite keeps it, so schema introspection on PostgreSQL reported the folded name and `autoUpdate`
proposed to add the declared one again on every run.

A PostgreSQL database created by an earlier version of this library has folded, lower-case names
for every mixed-case column, and `autoUpdate` against it now sees a column the target schema does
not declare — it will propose to drop `addedat` and add `addedAt`, losing the data in it. Rename
such columns by hand first:

```sql
ALTER TABLE t RENAME COLUMN createdat TO "createdAt";
```

A table name may not contain a dot: a dotted name is read as `schema.table` and quoted one
component at a time, which is what lets the library name PostgreSQL's `information_schema.columns`
catalogue.

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

### How a query becomes SQL

A `Query` is translated to a `FROM` clause together with, for each column of its view, the SQL
expression that computes that column in the scope of that `FROM`. Joins are therefore flat —
`FROM "author" AS "t1" CROSS JOIN "book" AS "t2"`, not a subquery per operand — and a query only
becomes a subquery where a clause cannot be merged into it, for instance a `WHERE` over a query
that already limits or groups its rows, a right-hand join operand whose columns the join has to be
able to null out, or a branch of a `UNION ALL` that orders or limits its rows — those clauses
belong to the compound statement and not to a branch of it. Such a subquery always carries an
alias, which is what PostgreSQL 15 and older require and which the generated SQL therefore now
satisfies. Every table occurrence is aliased too (`t1`, `t2`, …), so a table joined with itself
stays distinguishable and a correlated subquery can name an outer column unambiguously. Only the
outermost statement names its output columns, and it names them exactly as the view does, which is
how the backends decode the rows. `Query.project` generates no SQL at all: it renames and drops
output columns, and only that outermost `SELECT` list ever sees them.

Merging is also where the conditions of the operands are conjoined, and a `true` conjunct is
dropped as the conjunction is built rather than when it is printed: a query that filters nothing
starts from `true`, so without that a three-way join of unfiltered tables would read
`WHERE (((true) AND (true)) AND (true)) AND (...)` and hide the condition it does have.

A common table expression is the one thing that cannot stay where it was needed: `WITH` is legal
only at the top of a statement. So a translation carries the CTEs it needs, every combinator
carries its operands' along, and the outermost statement is the one that renders them — which is
why a `Query.recursive` buried under an `ORDER BY` or a join still comes out as a `WITH RECURSIVE`
in front of the whole statement.
