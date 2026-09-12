/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Interpretation.Basic

/-!
# Declarative migrations

`autoUpdate` introspects the live database and works out the operations that reach the declared
schema. That is the right thing in development and the wrong thing in production: what it does
depends on the database it happens to find, so two deployments of the same code can end up with
different schemas; it carries no data migrations; and it refuses a constraint change outright.

This module is the other way round. A migration is a named, ordered list of steps written in Lean
and committed with the code. `migrate` records in the database which of them have been applied and
applies the rest in order, so the schema is a function of the code alone. `Db.Migration.Generate`
writes the source of a migration that closes the gap between the declared schema and the schema the
committed migrations produce, and `Db.Migration.Cli` is the command-line front end.
-/

namespace Db.Migration

/--
One step of a migration.

`Step` lives in `Type 1` rather than `Type`, because `run` quantifies over the monad. That is not a
problem in practice: a `Step` is only ever passed to a function, never stored in one of the
library's `Type`-level structures or returned from a monad.
-/
inductive Step : Type 1 where
  /-- A change to the tables and columns, in the operation language `autoUpdate` uses. -/
  | schema (op : DatabaseOperation)
  /-- Create or drop an index. -/
  | index (op : IndexOperation)
  /-- A statement run as given, per dialect. The escape hatch for what the operation language does
  not say (constraint changes, data fix-ups in SQL). A raw statement is assumed to leave the schema
  as the schema operations around it describe: `makemigrations` cannot see into it.

  Named `rawSql` rather than `sql` so that the smart constructor `Step.sql`, which takes the one
  string that serves both dialects and is what almost every migration writes, can have the short
  name. `Step.sqlByDialect` is this constructor under a name that says what its function is for. -/
  | rawSql (statement : SQL.Dialect → String)
  /-- Arbitrary code in the database monad — a data migration written with the typed API.
  Polymorphic in the monad so that a migration is declared once and runs on either backend.

  The classes in the binder are exactly what the typed API needs: `DBMonadWithMigrations m`
  provides `DBMonad d m` for every `d`, and with `Monad m` that is enough for `DBMonad.lookup`,
  `DBMonad.insert`, `HasModel.fetch`, `HasModel.insert` and `HasModel.update`. `MonadExcept String`
  is deliberately *not* among them: nothing in the model layer needs it (it reports a failure
  through `DBMonadWithMigrations.abort`), and requiring it would rule out both backends, neither of
  which throws `String` — SQLite throws `IO.Error` and PostgreSQL its own `Exception`. -/
  | run (action : {m : Type → Type} → [Monad m] → [DBMonadWithMigrations m] → m Unit)

/--
A migration: a name, the steps it performs, and whether it is applied atomically.
-/
structure Migration : Type 1 where
  /-- Unique across the project; what the database records. Convention `NNNN_description`. -/
  name : String
  /-- The steps, applied in this order. -/
  steps : List Step
  /-- Whether the whole migration is applied in one transaction. Default on; a migration whose
  steps cannot run inside a transaction on the target backend (a column type change on SQLite
  rebuilds the table, which SQLite cannot do inside one) declares `atomic := false` and is then
  applied step by step, its record written after the last step. -/
  atomic : Bool := true

namespace Step

/-- Create a table.

The recipe's `indexes` are dropped: `CREATE TABLE` creates no indexes, and the backends' `execute`
ignores them, so keeping them would make the schema the migrations fold to claim indexes the
database does not have and `makemigrations` would never settle. Declare them as `createIndex`
steps after this one — which is what `Db.Migration.Generate.planSteps` emits. -/
def createTable (name : String) (table : TableRecipe) : Step :=
  .schema (.insert name { table with indexes := [] })

/-- Drop a table, and the data in it. -/
def dropTable (name : String) : Step :=
  .schema (.remove name)

/-- Rename a table, keeping its rows. -/
def renameTable (old new : String) : Step :=
  .schema (.rename old new)

/-- Add a column to an existing table. -/
def addColumn (table column : String) (c : Column) : Step :=
  .schema (.alter table (.insert column c))

/-- Drop a column, and the data in it. -/
def dropColumn (table column : String) : Step :=
  .schema (.alter table (.remove column))

/-- Rename a column, keeping its data. -/
def renameColumn (table old new : String) : Step :=
  .schema (.alter table (.rename old new))

/-- Change the type, nullability or default of an existing column. On SQLite this rebuilds the
table, so a migration containing one has to declare `atomic := false`. -/
def alterColumn (table column : String) (c : Column) : Step :=
  .schema (.alter table (.alter column c))

/-- Create an index. Its name has to be free: both backends require index names to be unique
across the whole database, not just within a table. -/
def createIndex (table : String) (idx : TableIndex String) : Step :=
  .index (.create table idx)

/-- Drop an index by name. The table is named too, so that the step says which table's schema it
changes without the reader having to look the index up. -/
def dropIndex (table name : String) : Step :=
  .index (.drop table name)

/-- One statement, the same text on both backends. -/
def sql (statement : String) : Step :=
  .rawSql fun _ => statement

/-- One statement, spelled per dialect — for the places the two backends disagree, such as the
function that gives the current time. -/
def sqlByDialect (statement : SQL.Dialect → String) : Step :=
  .rawSql statement

/-- A short description of a step, for error messages. -/
def describe : Step → String
  | .schema (.insert name _) => s!"create table `{name}`"
  | .schema (.remove name) => s!"drop table `{name}`"
  | .schema (.rename old new) => s!"rename table `{old}` to `{new}`"
  | .schema (.alter table (.insert column _)) => s!"add column `{table}`.`{column}`"
  | .schema (.alter table (.remove column)) => s!"drop column `{table}`.`{column}`"
  | .schema (.alter table (.rename old new)) =>
      s!"rename column `{old}` of `{table}` to `{new}`"
  | .schema (.alter table (.alter column _)) => s!"alter column `{table}`.`{column}`"
  | .index (.create table idx) => s!"create index `{idx.name}` on `{table}`"
  | .index (.drop table name) => s!"drop index `{name}` on `{table}`"
  | .rawSql _ => "a raw SQL statement"
  | .run _ => "a code step"

/-- Whether the step is a column change that SQLite realises by rebuilding the table, and which
therefore cannot be applied inside a transaction there.

The list mirrors the SQLite backend's own `needsRebuild`, which is the thing that decides: a type
or nullability change, of course, but also an `ADD COLUMN` SQLite rejects outright — a `NOT NULL`
column whose default is missing or `NULL`, or a column with a non-constant default. Leaving the
latter out would be worse than useless, since `ADD COLUMN` of a `NOT NULL` column is exactly what
`makemigrations` writes for a new non-optional field of a model. -/
def needsTableRebuildOnSqlite : Step → Bool
  | .schema (.alter _ (.alter _ _)) => true
  | .schema (.alter _ (.insert _ c)) =>
    match c.default? with
    | some (.call _) => true
    | some .null => !c.nullable
    | some _ => false
    | none => !c.nullable
  | _ => false

/-- The table recipe with every mention of the column `old` replaced by `new`.

A recipe names its columns by name in four more places than the column map: the primary key, the
`UNIQUE` groups, the columns of a foreign key, and the keys of an index. Both backends rewrite all
of them when they carry out a `RENAME COLUMN` — SQLite rewrites the stored `CREATE TABLE` and
`CREATE INDEX` texts, PostgreSQL holds them by attribute number — so a fold that renamed only the
key of the column map would claim a primary key over a column that no longer exists. Nothing could
then close the gap: `makemigrations` would report a constraint mismatch on the table for ever, and
the index would be proposed for dropping and re-creating on every run. -/
def renamedColumnRefs (r : TableRecipe) (old new : String) : TableRecipe :=
  letI rn := fun c => if c == old then new else c
  { r with
    primaryKey := r.primaryKey.map rn
    unique := r.unique.map (·.map rn)
    foreignKeys := r.foreignKeys.map fun fk => { fk with columns := fk.columns.map rn }
    indexes := r.indexes.map fun idx =>
      { idx with keys := idx.keys.map fun k => { k with column := rn k.column } } }

/-- Every table's foreign keys after the table `table` renamed its column `old` to `new`: a key
pointing at that table points at the new name, as it does in the database. -/
def retargetedColumn (tables : Std.HashMap String TableRecipe) (table old new : String) :
    Std.HashMap String TableRecipe :=
  tables.map fun _ r =>
    { r with
      foreignKeys := r.foreignKeys.map fun fk =>
        if fk.foreignTable == table then
          { fk with foreignColumns := fk.foreignColumns.map fun c => if c == old then new else c }
        else fk }

/-- Every table's foreign keys after the table `old` was renamed to `new`: a key pointing at it
follows the rename, as it does in the database. -/
def retargetedTable (tables : Std.HashMap String TableRecipe) (old new : String) :
    Std.HashMap String TableRecipe :=
  tables.map fun _ r =>
    { r with
      foreignKeys := r.foreignKeys.map fun fk =>
        if fk.foreignTable == old then { fk with foreignTable := new } else fk }

/-- Apply one step to the schema `s`, or say why it cannot be applied.

`rawSql` and `run` are schema-neutral by assumption: a raw statement is opaque, so the only
consistent reading is that the schema operations around it describe the whole of the change. -/
def apply (s : DatabaseRecipe) : Step → Except String DatabaseRecipe
  | .schema (.insert name recipe) =>
    if s.tables.contains name then
      .error s!"cannot create table `{name}`: a table of that name already exists"
    else
      -- Indexes are not part of a `CREATE TABLE`; see `Step.createTable`.
      .ok { tables := s.tables.insert name { recipe with indexes := [] } }
  | .schema (.remove name) =>
    if s.tables.contains name then .ok { tables := s.tables.erase name }
    else .error s!"cannot drop table `{name}`: there is no such table"
  | .schema (.rename old new) =>
    match s.tables[old]? with
    | none => .error s!"cannot rename table `{old}`: there is no such table"
    | some recipe =>
      if s.tables.contains new then
        .error s!"cannot rename table `{old}` to `{new}`: a table of that name already exists"
      else
        .ok { tables := retargetedTable ((s.tables.insert new recipe).erase old) old new }
  | .schema (.alter name op) =>
    match s.tables[name]? with
    | none => .error s!"cannot alter table `{name}`: there is no such table"
    | some recipe =>
      match op with
      | .insert column c =>
        if recipe.columns.contains column then
          .error s!"cannot add column `{name}`.`{column}`: the table already has one"
        else
          .ok { tables :=
            s.tables.insert name { recipe with columns := recipe.columns.insert column c } }
      | .remove column =>
        if recipe.columns.contains column then
          .ok { tables :=
            s.tables.insert name { recipe with columns := recipe.columns.erase column } }
        else .error s!"cannot drop column `{name}`.`{column}`: the table has no such column"
      | .rename old new =>
        match recipe.columns[old]? with
        | none => .error s!"cannot rename column `{name}`.`{old}`: the table has no such column"
        | some c =>
          if recipe.columns.contains new then
            .error s!"cannot rename column `{name}`.`{old}` to `{new}`: the table already has one"
          else
            -- The name has to follow into the constraints and indexes here and into the foreign
            -- keys of every other table, which is what the databases do; see `renamedColumnRefs`.
            letI renamed :=
              renamedColumnRefs
                { recipe with columns := (recipe.columns.insert new c).erase old } old new
            .ok { tables := retargetedColumn (s.tables.insert name renamed) name old new }
      | .alter column c =>
        if recipe.columns.contains column then
          .ok { tables :=
            s.tables.insert name { recipe with columns := recipe.columns.insert column c } }
        else .error s!"cannot alter column `{name}`.`{column}`: the table has no such column"
  | .index (.create table idx) =>
    match s.tables[table]? with
    | none => .error s!"cannot create index `{idx.name}`: there is no table `{table}`"
    | some recipe =>
      -- Both backends require an index name to be unique across the whole database, so the clash
      -- to look for is with any table's indexes, not just this one's.
      if s.tables.toList.any (fun (_, t) => t.indexes.any (·.name == idx.name)) then
        .error s!"cannot create index `{idx.name}`: an index of that name already exists"
      else
        .ok { tables := s.tables.insert table { recipe with indexes := recipe.indexes ++ [idx] } }
  | .index (.drop table name) =>
    match s.tables[table]? with
    | none => .error s!"cannot drop index `{name}`: there is no table `{table}`"
    | some recipe =>
      if recipe.indexes.any (·.name == name) then
        .ok { tables := s.tables.insert table
                { recipe with indexes := recipe.indexes.filter (·.name != name) } }
      else .error s!"cannot drop index `{name}`: table `{table}` has no such index"
  | .rawSql _ => .ok s
  | .run _ => .ok s

/-- Apply a list of steps in order. -/
def applyAll (s : DatabaseRecipe) (steps : List Step) : Except String DatabaseRecipe :=
  steps.foldlM Step.apply s

end Step

namespace Migration

/-- The schema after this migration's steps, starting from `s`, or which step is invalid against
the schema at that point and why. -/
def apply (s : DatabaseRecipe) (mig : Migration) : Except String DatabaseRecipe :=
  go s 1 mig.steps
where
  /-- The steps still to apply, numbered from `i` so that a failure says which one failed. -/
  go (cur : DatabaseRecipe) (i : Nat) : List Step → Except String DatabaseRecipe
    | [] => .ok cur
    | step :: rest =>
      match Step.apply cur step with
      | .ok next => go next (i + 1) rest
      | .error e => .error s!"migration `{mig.name}`, step {i} ({Step.describe step}): {e}"

/-- Whether the list of migrations is well formed: no two of them share a name, that name being
what the database records and hence how a migration is told from another. -/
def validate (ms : List Migration) : Except String Unit := do
  let mut seen : Std.HashSet String := ∅
  for m in ms do
    if seen.contains m.name then
      throw s!"the migration name `{m.name}` is used more than once"
    seen := seen.insert m.name
  return ()

/-- The schema the whole list of migrations produces, starting from nothing. -/
def foldAll (ms : List Migration) : Except String DatabaseRecipe := do
  validate ms
  ms.foldlM Migration.apply ∅

end Migration

/-! ### The tracking table

The table `migrate` records itself in, modelled with the library's own machinery rather than with
hand-written SQL: a one-table `Database`, so that reading and writing go through `DBMonad.lookup`
and `DBMonad.insert` and therefore work on every backend. `DBMonadWithMigrations m` provides
`DBMonad d m` for every `d`, so no extra instance is needed at the call site.
-/

/-- The columns of the tracking table. -/
inductive RecordIndex where
  /-- The migration's name, its primary key. -/
  | name
  /-- When it was applied, in seconds since the Unix epoch. -/
  | appliedAt
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString RecordIndex where
  toString
    | .name => "name"
    | .appliedAt => "applied_at"

instance : FromString RecordIndex where
  fromString
    | "name" => some .name
    | "applied_at" => some .appliedAt
    | _ => none

instance : Indexing RecordIndex where

/-- The table declared migrations are recorded in: one row per applied migration.

`applied_at` is an `int` of Unix seconds rather than a timestamp type, `DBType` having none. The
name is `text` rather than a bounded `varchar`, there being no length a migration name must not
exceed. -/
def trackingTable : Table where
  Index := RecordIndex
  columns
    | .name => { type := .text, nullable := false }
    | .appliedAt => { type := .int, nullable := false }
  primaryKey := [.name]

/-- The single table of `trackingDatabase`. -/
inductive TrackingIndex where
  | migrations
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString TrackingIndex where
  toString
    | .migrations => trackingTableName

instance : FromString TrackingIndex where
  fromString s := if s == trackingTableName then some .migrations else none

instance : Indexing TrackingIndex where
  -- The default tactic is `rfl`, which does not see through `trackingTableName`; unfolding the two
  -- instances above leaves `(if s == s then _ else _) = _`, which `simp` closes.
  fromString_toString
    | .migrations => by simp [FromString.fromString, ToString.toString]

/-- The one-table database the migration records live in. -/
def trackingDatabase : Database where
  Index := TrackingIndex
  tables
    | .migrations => trackingTable

variable {m : Type → Type} [Monad m] [DBMonadWithMigrations m]

open DBMonadWithMigrations in
/-- Create the tracking table if the database does not have it yet.

Checked against `currentDatabase` rather than issuing a `CREATE TABLE IF NOT EXISTS`, because the
operation language has no such operation and the introspection is there anyway. -/
def ensureTrackingTable : m Unit := do
  let current ← currentDatabase
  unless current.tables.contains trackingTableName do
    execute (.insert trackingTableName trackingTable.recipe)

/-- The names of the migrations the database records as applied, in name order — which for the
`NNNN_description` convention is the order they were applied in. -/
def applied : m (Array String) := do
  ensureTrackingTable
  let rows ← DBMonad.lookup (d := trackingDatabase)
    (.orderBy [{ column := RecordIndex.name }] (.all TrackingIndex.migrations))
  return rows.map fun row => row.value .name

/-- Record `name` as applied at `now` (Unix seconds). -/
def record (name : String) (now : Int) : m Unit :=
  DBMonad.insert (d := trackingDatabase) (name := TrackingIndex.migrations)
    { value
        | .name => some name
        | .appliedAt => some now }

open DBMonadWithMigrations in
/-- Carry out one step. -/
def Step.execute : Step → m Unit
  | .schema op => DBMonadWithMigrations.execute op
  | .index op => executeIndex op
  | .rawSql f => rawExecute (f (dialect (m := m)))
  | .run action => action

/-- Apply one migration and record it, without checking whether it has been applied already.

An `atomic` migration runs inside a transaction, so a step that fails leaves neither a half-applied
schema nor a record claiming the migration was applied. A migration that declares `atomic := false`
runs step by step and writes its record after the last one, which is the only thing to do when a
step cannot run in a transaction at all — a column type change on SQLite rebuilds the table, and
the foreign-key pragma that needs is a no-op inside a transaction. The price is that such a
migration can fail half way and has to be finished by hand; the record is written last so that a
failed one is at least not reported as applied. -/
def Migration.execute [DBMonadTransactional m] (mig : Migration) (now : Int) : m Unit :=
  letI body : m Unit := do
    mig.steps.forM Step.execute
    record mig.name now
  if mig.atomic then DBMonadTransactional.withTransaction body else body

open DBMonadWithMigrations in
/-- The names of the migrations the database has not recorded, in list order — what `migrate` would
apply if it ran now.

The *names* rather than the migrations themselves: `Migration` lives in `Type 1`, because a `run`
step quantifies over the monad, so `m (List Migration)` does not typecheck for `m : Type → Type`.
The name is what identifies a migration anyway, and `migrations.filter (·.name ∈ …)` recovers the
migrations for a caller that wants them. -/
def pending (migrations : List Migration) : m (Array String) := do
  match Migration.validate migrations with
  | .error e => abort e
  | .ok _ => pure ()
  let done ← applied
  return (migrations.map (·.name)).filter (!done.contains ·) |>.toArray

open DBMonadWithMigrations in
/--
Apply every migration in `migrations` that the database has not recorded, in list order, and record
each. Returns the names applied, in the order they were applied.

`now` is the time to record, in seconds since the Unix epoch. The class has no clock — a
`DBMonadWithMigrations` is not required to be over `IO`, and a migration that read the clock itself
would not be reproducible in a test — so the caller supplies it; `Db.Migration.Cli` takes it from
`Std.Time.Timestamp.now`.

Validated before anything is applied: the names have to be unique, and every name the database
records has to appear in the list. A recorded migration the code no longer knows means the database
is ahead of the code — a deployment rolled back, or a migration deleted rather than superseded —
and applying the remaining migrations on top of a schema whose history is unknown is how a schema
ends up in a state no code describes.
-/
def migrate [DBMonadTransactional m] (migrations : List Migration) (now : Int) :
    m (Array String) := do
  match Migration.validate migrations with
  | .error e => abort e
  | .ok _ => pure ()
  ensureTrackingTable
  let done ← applied
  let known : Std.HashSet String := .ofList (migrations.map (·.name))
  letI unknown := done.filter (!known.contains ·)
  unless unknown.isEmpty do
    abort <|
      s!"the database records the migration(s) {", ".intercalate unknown.toList}, which this " ++
      "code does not declare. The database is ahead of the code; deploy the code that declares " ++
      "them, or remove the record by hand if they were withdrawn."
  let mut res := #[]
  for mig in migrations do
    unless done.contains mig.name do
      mig.execute now
      res := res.push mig.name
  return res

end Db.Migration
