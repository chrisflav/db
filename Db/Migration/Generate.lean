/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Migration.Declarative

/-!
# `makemigrations`: writing the migration that closes the gap

The declared schema — the tables the codebase says it has — and the schema the committed migrations
fold to are two `DatabaseRecipe`s. When they differ, the difference is a migration that has not been
written yet. `planSteps` computes its steps and `render` writes them out as the source of a Lean
module.

The source is printed by explicit printers rather than by a derived `Repr`. `Repr` prints a
structure with every field, including the ones at their default, and prints a `Std.HashMap` as its
internal representation, neither of which is source anybody wants to read or edit — and the point
of a generated migration is that it is committed and edited like any other code.
-/

namespace Db.Migration

/-! ### Printing Lean source -/

namespace Source

/-- `n` spaces. -/
private def spaces (n : Nat) : String :=
  String.ofList (List.replicate n ' ')

/-- Indent every line of `s` by `n` spaces except the first, which the caller has already placed. -/
def indentTail (n : Nat) (s : String) : String :=
  match s.splitOn "\n" with
  | [] => s
  | first :: rest => "\n".intercalate (first :: rest.map fun l => spaces n ++ l)

/-- Lean source for a string literal. `repr` is what escapes it correctly — a quote, a backslash or
a newline in a table name would otherwise produce a file that does not parse. -/
def str (s : String) : String :=
  toString (repr s)

/-- Lean source for an integer literal. A negative one is parenthesised, since `.int -1` parses as
a subtraction. -/
def int (n : Int) : String :=
  if n < 0 then s!"({n})" else toString n

/-- Lean source for a list of string literals. -/
def strings (l : List String) : String :=
  "[" ++ ", ".intercalate (l.map str) ++ "]"

def dbType : DBType → String
  | .bool => ".bool"
  | .int => ".int"
  | .varchar n => s!".varchar {n}"
  | .text => ".text"

def columnDefault : ColumnDefault → String
  | .int n => s!".int {int n}"
  | .str s => s!".str {str s}"
  | .bool b => s!".bool {b}"
  | .null => ".null"
  | .call fn => s!".call {str fn}"

/-- Lean source for a column. Fields at their default are omitted: the generated source is read and
edited, and `default? := none, autoIncrement := false` on every column is noise. -/
def column (c : Column) : String :=
  letI fields :=
    [s!"type := {dbType c.type}", s!"nullable := {c.nullable}"] ++
    (match c.default? with
      -- Parenthesised: `some .int 0` would parse as `some` applied to two arguments.
      | some d => [s!"default? := some ({columnDefault d})"]
      | none => []) ++
    (if c.autoIncrement then ["autoIncrement := true"] else [])
  "{ " ++ ", ".intercalate fields ++ " }"

def foreignKeyAction : ForeignKeyAction → String
  | .noAction => ".noAction"
  | .restrict => ".restrict"
  | .cascade => ".cascade"
  | .setNull => ".setNull"
  | .setDefault => ".setDefault"

def foreignKey (fk : ForeignKey String) : String :=
  letI fields :=
    [s!"columns := {strings fk.columns}", s!"foreignTable := {str fk.foreignTable}",
     s!"foreignColumns := {strings fk.foreignColumns}"] ++
    (if fk.onDelete == .noAction then [] else [s!"onDelete := {foreignKeyAction fk.onDelete}"]) ++
    (if fk.onUpdate == .noAction then [] else [s!"onUpdate := {foreignKeyAction fk.onUpdate}"])
  "{ " ++ ", ".intercalate fields ++ " }"

def sortDirection : SortDirection → String
  | .asc => ".asc"
  | .desc => ".desc"

def collation : Collation → String
  | .binary => ".binary"
  | .caseInsensitive => ".caseInsensitive"

def indexKey (k : IndexKey String) : String :=
  letI fields :=
    [s!"column := {str k.column}"] ++
    (if k.direction == .asc then [] else [s!"direction := {sortDirection k.direction}"]) ++
    (if k.collation == .binary then [] else [s!"collation := {collation k.collation}"])
  "{ " ++ ", ".intercalate fields ++ " }"

def tableIndex (i : TableIndex String) : String :=
  letI fields :=
    [s!"name := {str i.name}",
     "keys := [" ++ ", ".intercalate (i.keys.map indexKey) ++ "]"] ++
    (if i.unique then ["unique := true"] else [])
  "{ " ++ ", ".intercalate fields ++ " }"

/-- Lean source for a table recipe, over as many lines as its columns need.

The indexes are not printed: `Step.createTable` drops them, `CREATE TABLE` creating no indexes, and
`planSteps` emits a `createIndex` step for each of them instead. -/
def tableRecipe (r : TableRecipe) : String :=
  letI cols := r.columns.toList.map fun (n, c) => s!"({str n}, {column c})"
  letI fields :=
    ["columns := .ofList\n    [" ++ ",\n     ".intercalate cols ++ "]"] ++
    (if r.primaryKey.isEmpty then [] else [s!"primaryKey := {strings r.primaryKey}"]) ++
    (if r.unique.isEmpty then []
      else ["unique := [" ++ ", ".intercalate (r.unique.map strings) ++ "]"]) ++
    (if r.foreignKeys.isEmpty then []
      else
        ["foreignKeys :=\n    [" ++ ",\n     ".intercalate (r.foreignKeys.map foreignKey) ++ "]"])
  "{ " ++ ",\n  ".intercalate fields ++ " }"

/-- Lean source for one step, or `none` for a `run` step, whose action is arbitrary Lean code and
cannot be recovered from the value.

A `rawSql` step *can* be printed, by evaluating its function on both dialects: that is the whole of
what it is. -/
def step : Step → Option String
  | .schema (.insert name recipe) =>
    some s!".createTable {str name}\n  {indentTail 2 (tableRecipe recipe)}"
  | .schema (.remove name) => some s!".dropTable {str name}"
  | .schema (.rename old new) => some s!".renameTable {str old} {str new}"
  | .schema (.alter table (.insert col c)) =>
    some s!".addColumn {str table} {str col} {column c}"
  | .schema (.alter table (.remove col)) => some s!".dropColumn {str table} {str col}"
  | .schema (.alter table (.rename old new)) =>
    some s!".renameColumn {str table} {str old} {str new}"
  | .schema (.alter table (.alter col c)) =>
    some s!".alterColumn {str table} {str col} {column c}"
  | .index (.create table idx) => some s!".createIndex {str table} {tableIndex idx}"
  | .index (.drop table name) => some s!".dropIndex {str table} {str name}"
  | .rawSql f =>
    if f .postgres == f .sqlite then some s!".sql {str (f .postgres)}"
    else
      some <|
        ".sqlByDialect fun\n" ++
        s!"    | .postgres => {str (f .postgres)}\n" ++
        s!"    | .sqlite => {str (f .sqlite)}"
  | .run _ => none

end Source

/-- The steps that take the schema `migrations` produce to `target`, or the reason none can be
written.

Two things make it impossible. A migration list that does not fold — a step invalid against the
schema at that point, or a duplicated name — has no source schema to diff against. And a table whose
constraints differ between the two: the operation language says column changes only, so a constraint
change cannot be written as a step, and reporting it is what keeps it from being generated as a
silent no-op. Write that one by hand as a `Step.sql`, exactly as `autoUpdate` asks for.

An empty result means the declared schema and the migrations already agree. -/
-- Written with explicit `match`es rather than in `do`: `Except String` is a monad only on types in
-- `String`'s own universe, and `List Step` is one universe up, `Step` quantifying over the monad.
def planSteps (migrations : List Migration) (target : DatabaseRecipe) :
    Except String (List Step) :=
  match Migration.foldAll migrations with
  | .error e => .error e
  | .ok source =>
    let mismatches := source.constraintMismatches target
    if !mismatches.isEmpty then
      .error <|
        s!"the constraints of the table(s) {", ".intercalate mismatches.toList} differ from " ++
        "those of the declared schema. A constraint change on an existing table cannot be " ++
        "written in the operation language; write it by hand as a `Step.sql` step, or drop and " ++
        "recreate the tables."
    else
      let schemaSteps := (source.operations target).toList.map Step.schema
      -- The index operations are computed against the schema *after* the column operations, as in
      -- `autoUpdate` and for the same reason: an index on a column this migration adds cannot be
      -- created before the column exists, and a table this migration creates starts with none.
      match Step.applyAll source schemaSteps with
      | .error e => .error e
      | .ok migrated =>
        .ok (schemaSteps ++ (migrated.declaredIndexOperations target).toList.map Step.index)

/-- Turn a migration name into the identifier the generated definition is bound to. Anything that
is not a letter, a digit or an underscore becomes an underscore; the `migration_` prefix the caller
puts in front is what keeps a name starting with a digit from being a bad identifier. -/
def identifierOfName (name : String) : String :=
  String.ofList (name.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')

/-- Lean source for a migration named `name` with these steps: a complete module, ready to be
written to a file, compiled and committed.

Two comments may be emitted above the list. A step SQLite realises by rebuilding the table — a
column `alter`, or an `ADD COLUMN` of a `NOT NULL` column without a constant default, which is what
a new non-optional model field plans to — cannot happen inside a transaction there, so the
migration may have to be `atomic := false`; may, because it depends on the backend it is applied
to, which the generator does not know, so it says so and leaves `atomic` at its default rather than
deciding for the reader. And a `run` step, being arbitrary Lean code, cannot be printed at all;
that only arises when `render` is called on a hand-built list, never on a plan, but it is reported
rather than dropped in silence. -/
def render (name : String) (steps : List Step) : String :=
  letI entries := steps.filterMap Source.step
  letI notes :=
    (if steps.any Step.needsTableRebuildOnSqlite then
      ["  -- A column type or nullability change, and adding a `NOT NULL` column without a",
       "  -- constant default, rebuild the table on SQLite, which cannot run inside a transaction",
       "  -- there; set `atomic := false` if this migration is applied to SQLite."]
    else []) ++
    (if entries.length < steps.length then
      ["  -- One or more code steps were left out: a `Step.run` step is arbitrary Lean code and",
       "  -- cannot be written back as source. Re-add them by hand."]
    else [])
  letI body :=
    if entries.isEmpty then "  steps := []"
    else
      "  steps := [\n    " ++ ",\n    ".intercalate (entries.map (Source.indentTail 4)) ++ "\n  ]"
  String.intercalate "\n" <|
    ["import Db", "",
     "/-- Generated by `makemigrations`; edit freely. -/",
     s!"def migration_{identifierOfName name} : Db.Migration.Migration where",
     s!"  name := {Source.str name}"] ++ notes ++ [body, ""]

/-- The `NNNN` a new migration takes: one more than the highest leading number among the names of
the migrations there are, and `0001` when there are none. Four digits, zero-padded, which is what
makes the names sort in the order they were created. -/
def nextNumber (migrations : List Migration) : String :=
  letI highest := migrations.foldl (init := 0) fun acc mig =>
    max acc ((mig.name.takeWhile Char.isDigit).toNat?.getD 0)
  letI digits := toString (highest + 1)
  (String.ofList (List.replicate (4 - digits.length) '0')) ++ digits

end Db.Migration
