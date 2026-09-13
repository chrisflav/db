/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Schema

/-!
# The query keywords are not reserved

`guard`, `select`, `order_by`, `order_by_desc`, `limit`, `offset` and the `v"..."` prefix are
declared as non-reserved symbols, so importing `Db` does not take those words away from the rest of
a program. This module is the proof: it uses every one of them as an ordinary identifier — a field,
a binder, core's `guard` in a `do` block — and then again, in the same file, as a clause of a
`query% do` block, where they mean what the DSL says they mean.

The module has nothing to run; it is checked when it is built, which is what makes it a regression
test for the tokens.
-/

namespace IdentifierExample

open BookExample Db.Query.DSL

/-- A window onto a result, with the fields a paginated API would give it. Before the keywords
were made non-reserved, none of these three names could be written in a module importing `Db`. -/
structure Page where
  /-- How many rows the page holds. -/
  limit : Nat
  /-- How many rows precede it. -/
  offset : Nat
  /-- The column the page is sorted by. -/
  select : String
  deriving Repr

/-- The first page of ten, by title. -/
def firstPage : Page := { limit := 10, offset := 0, select := "title" }

/-- The rows of `p`, as a half-open range. `v` here is an ordinary parameter, not the prefix of a
`VarChar` literal: the two are told apart by the string that must follow the prefix with no space
in between. -/
def rangeOf (p : Page) (v : Nat) : Nat × Nat :=
  (p.offset + v, p.offset + v + p.limit)

#guard rangeOf firstPage 5 == (5, 15)

/-- Core's `guard`, in the `do` block over `Option` that is its usual home. -/
def halfOfEven (n : Nat) : Option Nat := do
  guard (n % 2 = 0)
  return n / 2

#guard halfOfEven 10 == some 5
#guard halfOfEven 7 == none

/-- The same words as the DSL's clauses: a filter, a projection, a case-folding sort, a window —
and a `v"..."` literal in the condition. -/
def pagedTitles : QuerySet Book := query% do
  let b ← from Book
  let a ← from Author
  guard b.author = a.name
  guard a.name ≠ v"Nobody"
  select b
  order_by b.title nocase
  limit 10
  offset 20

/-- And with the identifiers of this module standing next to them, in one string. -/
def describe (p : Page) : String :=
  s!"{p.select}: {p.limit} rows from {p.offset}, {rangeOf p 0}"

#guard describe firstPage == "title: 10 rows from 0, (0, 10)"

end IdentifierExample
