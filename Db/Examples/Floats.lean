/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Schema

/-!
# The floating-point demo

One demo, run on both backends, for the `float` column type. What it checks is a round trip: a
value written and read back has to be the value that was written, bit for bit. That is not free on
either side — Lean's `Float.toString` prints six decimals, so `1e-7` would go into the database as
`0.000000`, and both backends hand a value back as text, which only says everything if it is
printed at enough digits — and it is the same round trip on both, so it is written once.
-/

namespace FloatExample

open BookExample HasModel DBMonadWithMigrations Db.Query.DSL

variable {m : Type → Type} [Monad m] [DBMonadWithMigrations m] [MonadLiftT IO m]

/-- The values a round trip has to survive: the ones whose decimal spelling needs all seventeen
digits, the ones `Float.toString` prints as `0.000000`, both extremes of the format, and a few
ordinary numbers. -/
def samples : List Float :=
  [0.1, 1e-7, 123456789.123456789, 1e20, 4.0, -2.5, 0.30000000000000004, 5e-324,
   1.7976931348623157e308, 0.0, 1.0]

/-- The output view of "the mean and the largest of `value`", over the whole table: an `AVG` is a
`float` whatever it is taken of, and it is `NULL` for an empty table as every aggregate but a
`COUNT` is. -/
inductive StatsIndex where
  | average
  | largest
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString StatsIndex where
  toString
    | .average => "average"
    | .largest => "largest"

instance : FromString StatsIndex where
  fromString
    | "average" => some .average
    | "largest" => some .largest
    | _ => none

instance : Indexing StatsIndex where

def statsView : View (%database mydb) where
  Index := StatsIndex
  name
    | .average => .computation "average" { type := .float, nullable := true }
    | .largest => .computation "largest" { type := .float, nullable := true }

/-- `SELECT AVG(value), MAX(value) FROM sample`. -/
def stats : Query (%database mydb) statsView :=
  .aggregate
    { entry
        | .average => .apply .avg SampleIndex.value
        | .largest => .apply .max SampleIndex.value }
    (.all (HasModel.model Sample).index)

/-- Write each of the awkward values, read it back, and compare the bits. Then compare a float
column with a `Float` constant of the query, which the DSL embeds as a literal, and take an average,
which is the aggregate a floating-point type is what was missing for. -/
def floatDemo (label : String) : m Unit := do
  autoUpdate (%database mydb)
  -- The PostgreSQL database is shared between the demos and keeps what the last run left.
  let _ ← HasModel.delete (α := Sample) .true
  IO.println s!"Float round trips ({label}):"
  let mut exact := true
  for x in samples do
    let row ← HasModel.insertReturning ({ id := 0, value := x, margin := some x } : Sample)
    let ok := row.value.toBits == x.toBits && (row.margin.map Float.toBits) == some x.toBits
    exact := exact && ok
    IO.println s!"  {Float.toDecimalString x} -> {Float.toDecimalString row.value}, exact: {ok}"
  IO.println s!"  every value survived the round trip: {exact}"
  -- A `NULL` in a nullable float column is not a zero.
  let absent ← HasModel.insertReturning ({ id := 0, value := 2.5, margin := none } : Sample)
  IO.println s!"  a missing margin reads back as: {absent.margin.map Float.toDecimalString}"
  -- A `Float` constant of the query is embedded as a literal, so the comparisons work on a float
  -- column exactly as they do on an integer one.
  let big ← fetch <| query% do
    let s ← from Sample
    guard s.value > 1.0
    select s
  IO.println s!"  values greater than 1.0: {big.size}"
  let tiny ← fetch <| query% do
    let s ← from Sample
    guard s.value ≤ 1e-7
    select s
  IO.println s!"  values at most 1e-7: {tiny.size}"
  -- `AVG` needs a floating-point type to give its result, which is what it was missing.
  for row in ← DBMonad.lookup stats do
    IO.println <|
      s!"  average: {(row.value .average).map Float.toDecimalString}, " ++
      s!"largest: {(row.value .largest).map Float.toDecimalString}"
  -- The fixed point: the type a float column is declared with has to be the one introspection
  -- reads back, or `autoUpdate` proposes to change the column on every run.
  autoUpdate (%database mydb)
  let current ← currentDatabase
  IO.println <|
    s!"  pending operations after two autoUpdates: " ++
    s!"{(current.operations (%database mydb).recipe).size}, the type read back for " ++
    s!"`sample`.`value`: {repr ((current.tables["sample"]?.bind (·.columns["value"]?)).map (·.type))}"
  -- The rows are this demo's to clean up: the next run of the suite starts from an empty table on
  -- SQLite and should on PostgreSQL too.
  let _ ← HasModel.delete (α := Sample) .true

end FloatExample
