/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Schema

/-!
# The recursive-query demo

One demo, run on both backends, for `Query.recursive`: the ancestor walk of the README, over a
`node` table holding a chain, an unrelated row, and a two-node cycle. The generated SQL is printed
once, and the shape that matters — the step's reference to the CTE standing directly in its `FROM`
rather than inside a subquery — is asserted rather than left to the reader, SQLite being the
backend that rejects the other shape with `circular reference: ancestors`.

Shared between the two backends rather than written twice: the SQL is the same on both, and a
difference between the two printouts would be the interesting thing here.
-/

namespace RecursiveExample

open BookExample HasModel DBMonadWithMigrations

/-- The `node` table, as an index into the example database. -/
abbrev nodeIndex : (%database mydb).Index := (HasModel.model Node).index

/-- The column the walk counts its steps in.

Named once and shared by the base, the step and the projection below: the `View.Hom` of that
projection holds by `rfl` only because the two views mean the very same `Column` by `depth`. -/
abbrev depthColumn : Column := { type := .int, nullable := false }

/-- The view the walk produces: a `node` row, and how many steps from the start it was found at.

Its columns are named `left__id`, `left__parent`, `left__title` and `right__depth`, which is what
the CTE declares them as and what the step's reference to the CTE reads them back by. -/
abbrev ancestorView : View (%database mydb) :=
  (Table.view nodeIndex).prod (View.singleton (%database mydb) "depth" depthColumn)

/--
The ancestor walk: the node `start`, then its parent, then that node's parent, and so on, each row
carrying its distance from `start`.

The step stops at `bound`, which is what keeps a cycle among the `parent` references from looping
forever: `UNION ALL` returns a row every time it is reached, so nothing else would.

This is the worked example of the README, and the indices are the awkward part of writing it by
hand. The step joins the rows found so far with the whole table, so its view is
`(node × depth) × node`: `Sum.inl (Sum.inl _)` is a column of a row found so far,
`Sum.inl (Sum.inr ⟨⟩)` is that row's depth, and `Sum.inr _` is a column of the candidate parent.
The `extend` puts the new depth next to all of that, and the `project` brings the result back onto
`ancestorView`, which is the view `base` and `step` have to agree on.
-/
def ancestorsOf (start : Int) (bound : Int := 64) : Query (%database mydb) ancestorView :=
  .recursive "ancestors"
    -- The base: the row to start from, at depth 0.
    (.extend "depth" depthColumn (.int 0)
      (.filter (.eq (.var NodeIndex.id .int) (.int start)) (.all nodeIndex)))
    -- The step: for every row found so far, the node its `parent` names, one step deeper. A row
    -- whose `parent` is `NULL` matches nothing, which is how a walk that reaches a root stops.
    (.project
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
          (.join (.cteRef "ancestors" ancestorView) (.all nodeIndex)))))

/-- The walk, sorted by depth, so that the printed rows come out in the order the walk found them
whatever the planner did. The `WITH` is hoisted past the `ORDER BY` to the top of the statement,
which is the only place SQL allows it. -/
def sortedAncestorsOf (start : Int) (bound : Int := 64) : Query (%database mydb) ancestorView :=
  .orderBy [{ column := Sum.inr ⟨⟩ }] (ancestorsOf start bound)

/-- Print a recursive statement, and check that its step names the CTE directly rather than through
a subquery.

That is SQLite's rule — a self-reference inside a subquery is rejected with
`circular reference: ancestors` — and a subquery per join operand is exactly what the translator
produced before joins were flattened, so the demo asserts it instead of leaving it to the reader:
the text after `UNION ALL` must contain no nested `SELECT`, and there must be exactly one such
union. The two spellings are the two the renderer can produce, `( SELECT` for a subquery in a
`FROM` and `(SELECT` for one used as a value. -/
def printRecursiveSql (label : String) (sql : String) : IO Unit := do
  IO.println s!"{label}: {sql}"
  match sql.splitOn " UNION ALL " with
  | [_, step] =>
    if (step.splitOn "( SELECT").length != 1 || (step.splitOn "(SELECT").length != 1 then
      throw <| IO.userError <|
        s!"the recursive step of `{label}` reaches the CTE through a subquery, which SQLite " ++
          "rejects as a circular reference"
  | _ =>
    throw <| IO.userError s!"the SQL for `{label}` is not a single `UNION ALL`"

/-- Report how many rows the bounded walk of the cycle returned, and insist on the number the
bound gives: 64 steps on top of the row the walk started from. A walk that came back with fewer
would have terminated for the wrong reason, and the demo would no longer be showing anything. -/
def reportCycleRows (rows : Nat) : IO Unit := do
  IO.println s!"  rows walked out of the cycle at 10, bounded at depth 64: {rows}"
  unless rows == 65 do
    throw <| IO.userError s!"the bounded walk of the cycle returned {rows} rows, not 65"

variable {m : Type → Type} [Monad m] [DBMonadWithMigrations m] [MonadLiftT IO m]

/-- Exercise `Query.recursive` end to end: an ancestor walk up a chain, and the same walk started
inside a cycle, where the depth bound in the step is what makes it terminate. -/
def recursiveDemo (label : String) : m Unit := do
  autoUpdate (%database mydb)
  -- The PostgreSQL database is shared between the demos and keeps what the last run left.
  let _ ← HasModel.delete (α := Node) .true
  -- The ids are written out rather than left to the database: the walk is about which row points
  -- at which, and that is easier to read with the ids in the source.
  let node (id : Int) (parent : Option Int) (title : VarChar 100) :
      (HasModel.database Node).Insert (HasModel.model Node).index :=
    { value
        | NodeIndex.id => some id
        | NodeIndex.parent => some parent
        | NodeIndex.title => some title }
  -- The chain 1 ← 2 ← 3 ← 4, a node belonging to no chain, and the cycle 10 ↔ 11.
  DBMonad.insert (d := HasModel.database Node) (node 1 none (v"root"))
  DBMonad.insert (d := HasModel.database Node) (node 2 (some 1) (v"branch"))
  DBMonad.insert (d := HasModel.database Node) (node 3 (some 2) (v"twig"))
  DBMonad.insert (d := HasModel.database Node) (node 4 (some 3) (v"leaf"))
  DBMonad.insert (d := HasModel.database Node) (node 5 none (v"unrelated"))
  DBMonad.insert (d := HasModel.database Node) (node 10 (some 11) (v"cycle a"))
  DBMonad.insert (d := HasModel.database Node) (node 11 (some 10) (v"cycle b"))
  IO.println s!"Recursive queries ({label}):"
  let walk := sortedAncestorsOf 4
  printRecursiveSql "  ancestors of 4" (SQL.Select.fromQuery walk).toString
  for row in ← DBMonad.lookup walk do
    IO.println <|
      s!"    depth {row.value (Sum.inr ⟨⟩)}: " ++
      s!"{row.value (Sum.inl NodeIndex.id)} {row.value (Sum.inl NodeIndex.title)}"
  -- The same walk, started inside the cycle. Without the bound in the step this query does not
  -- terminate at all; with it, it stops at the bound.
  reportCycleRows (← DBMonad.lookup (sortedAncestorsOf 10)).size

end RecursiveExample
