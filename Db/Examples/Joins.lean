/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Schema

/-!
# The join demos

One demo, run on both backends, for the shape of the SQL a join translates to: joins are emitted
flat, and a query only becomes a subquery when a clause cannot be merged into it. The SQL is
printed, and the cases that must not nest assert it rather than leaving it to the reader.

Shared between the two backends rather than written twice, because the SQL is the same on both and
a difference between the two printouts would be the interesting thing here.
-/

namespace JoinExample

open BookExample HasModel DBMonadWithMigrations

variable {m : Type → Type} [Monad m] [DBMonadWithMigrations m] [MonadLiftT IO m]

/-- Print lines in a fixed order.

A join's rows come back in whatever order the planner produced them, which is not the same on the
two backends and is not what these demos are about; sorting the printed lines makes the demo say
what it means without an `ORDER BY` in every query. -/
def printSorted (lines : Array String) : IO Unit := do
  for line in lines.qsort (· < ·) do
    IO.println line

/-- Exercise the flat translation of joins end to end: a filtered cross join, a self join filtered
on both sides, a left join whose right side is filtered, a join with a limited operand, a
correlated count over a joined outer query, a projection, and the two ways of nesting a product.

Every query here is also a decoding test: a nested product names its columns `left__left__title`,
and the translator has to give the `SELECT` list exactly the names the view asks for or the rows
cannot be read back. -/
def joinDemo (label : String) : m Unit := do
  autoUpdate (%database mydb)
  -- The PostgreSQL database is shared between the demos and keeps what the last run left.
  let _ ← HasModel.delete (α := Book) .true
  let _ ← HasModel.delete (α := Author) .true
  let _ ← HasModel.delete (α := ReadingList) .true
  let nora : Author := { name := v"Nora", age := 41, retired := false }
  let sequel : Book := { title := v"A drama, the sequel", author := lisa.name, year := some 2020 }
  let anon : Book := { title := v"Anonymous", author := v"Nobody", year := none }
  insert mike
  insert lisa
  insert nora
  insert novel
  insert drama
  insert sequel
  insert anon
  insert ({ order := 1, addedAt := 20260101, «select» := true,
            bookTitle := novel.title } : ReadingList)
  insert ({ order := 2, addedAt := 20260202, «select» := false,
            bookTitle := drama.title } : ReadingList)
  let authorTable := (HasModel.model Author).index
  let bookTable := (HasModel.model Book).index
  let listTable := (HasModel.model ReadingList).index
  IO.println s!"Joins ({label}):"
  -- A cross join with a condition relating the two sides, which is what an inner join is. Both
  -- tables stand in the one `FROM`, and the condition is one `WHERE` over them.
  let inner : Query (%database mydb) _ :=
    .filter
      (.and
        (.eq (.var (Sum.inl AuthorIndex.name) (.varchar 100))
             (.var (Sum.inr BookIndex.author) (.varchar 100)))
        (.var (Sum.inl AuthorIndex.retired) .bool))
      (.join (.all authorTable) (.all bookTable))
  printFlatSql "  inner join" (SQL.Select.fromQuery inner).toString
  printSorted <| (← DBMonad.lookup inner).map fun row =>
    s!"    {row.value (Sum.inl AuthorIndex.name)} wrote {row.value (Sum.inr BookIndex.title)}"
  -- A table joined with itself, filtered on both sides. The two occurrences get different aliases,
  -- which is what lets the condition say which of the two it means.
  let pairs : Query (%database mydb) _ :=
    .filter
      (.and
        (.eq (.var (Sum.inl AuthorIndex.retired) .bool)
             (.var (Sum.inr AuthorIndex.retired) .bool))
        (.lt (.var (Sum.inl AuthorIndex.name) (.varchar 100))
             (.var (Sum.inr AuthorIndex.name) (.varchar 100))))
      (.join (.filter (.gt (.var AuthorIndex.age .int) (.int 20)) (.all authorTable))
             (.filter (.gt (.var AuthorIndex.age .int) (.int 20)) (.all authorTable)))
  printFlatSql "  self join" (SQL.Select.fromQuery pairs).toString
  printSorted <| (← DBMonad.lookup pairs).map fun row =>
    s!"    {row.value (Sum.inl AuthorIndex.name)} and " ++
    s!"{row.value (Sum.inr AuthorIndex.name)} agree on retired"
  -- A left join whose right-hand side is filtered. The filter has to end up in the `ON`: as a
  -- `WHERE` it would delete exactly the rows the outer join was for.
  let retiredOnly : Query (%database mydb) _ :=
    .leftJoin (.all bookTable)
      (.filter (.var AuthorIndex.retired .bool) (.all authorTable))
      (.eq (.var (Sum.inl BookIndex.author) (.varchar 100))
           (.var (Sum.inr AuthorIndex.name) (.varchar 100)))
  printFlatSql "  left join over a filtered right side" (SQL.Select.fromQuery retiredOnly).toString
  printSorted <| (← DBMonad.lookup retiredOnly).map fun row =>
    s!"    {row.value (Sum.inl BookIndex.title)} — " ++
    s!"retired author {row.value (Sum.inr AuthorIndex.name)}"
  -- A join one of whose sides limits its rows. That side cannot be merged into the join — the
  -- limit would then apply to the join — so it becomes a subquery, with an alias.
  let limited : Query (%database mydb) _ :=
    .join (.limit 1 (.orderBy [{ column := AuthorIndex.name }] (.all authorTable)))
      (.all bookTable)
  printAliasedSql "  join with a limited side" (SQL.Select.fromQuery limited).toString
  let limitedRows ← DBMonad.lookup limited
  IO.println <|
    s!"    {limitedRows.size} row(s), all for " ++
    s!"{(limitedRows[0]?.map (fun r => toString (r.value (Sum.inl AuthorIndex.name)))).getD "?"}"
  -- A correlated count over an outer query that is itself a join: the outer aliases and the
  -- subquery's have to stay distinct across the two scopes for the correlation to mean anything.
  let pairCounts : Query (%database mydb) _ :=
    .correlate "books"
      (.filter
        (.eq (.var (Sum.inl AuthorIndex.name) (.varchar 100))
             (.var (Sum.inr AuthorIndex.name) (.varchar 100)))
        (.join (.all authorTable) (.all authorTable)))
      (.all bookTable)
      (.eq (.var (Sum.inr BookIndex.author) (.varchar 100))
           (.var (Sum.inl (Sum.inl AuthorIndex.name)) (.varchar 100)))
      .countAll
  IO.println s!"  correlated count over a self join: {(SQL.Select.fromQuery pairCounts).toString}"
  printSorted <| (← DBMonad.lookup pairCounts).map fun row =>
    s!"    {row.value (Sum.inl (Sum.inl AuthorIndex.name))} wrote " ++
    s!"{row.value (Sum.inr ⟨⟩)} book(s)"
  -- A projection generates no SQL at all: it renames and drops output columns, which only the
  -- `SELECT` list at the top ever sees.
  let projected : Query (%database mydb) _ :=
    .project (View.sumInr (Table.view authorTable) (Table.view bookTable)) inner
  printFlatSql "  projection of a join" (SQL.Select.fromQuery projected).toString
  printSorted <| (← DBMonad.lookup projected).map fun row => s!"    {row.value BookIndex.title}"
  -- A product nested to the left, `(a × b) × c`, whose columns are `left__left__name` and so on.
  -- The condition touches all three sides.
  let leftNested : Query (%database mydb) _ :=
    .filter
      (.and
        (.and
          (.eq (.var (Sum.inl (Sum.inl AuthorIndex.name)) (.varchar 100))
               (.var (Sum.inl (Sum.inr BookIndex.author)) (.varchar 100)))
          (.eq (.var (Sum.inr ReadingListIndex.bookTitle) (.varchar 200))
               (.var (Sum.inl (Sum.inr BookIndex.title)) (.varchar 200))))
        (.var (Sum.inl (Sum.inl AuthorIndex.retired)) .bool))
      (.join (.join (.all authorTable) (.all bookTable)) (.all listTable))
  printFlatSql "  three-way join, nested left" (SQL.Select.fromQuery leftNested).toString
  printSorted <| (← DBMonad.lookup leftNested).map fun row =>
    s!"    {row.value (Sum.inl (Sum.inl AuthorIndex.name))}: " ++
    s!"{row.value (Sum.inl (Sum.inr BookIndex.title))} " ++
    s!"at position {row.value (Sum.inr ReadingListIndex.order)}"
  -- The same product nested to the right, `a × (b × c)`. The right-hand operand of a join is
  -- parenthesised when it is itself a join, or the `CROSS JOIN` would re-associate.
  let rightNested : Query (%database mydb) _ :=
    .filter
      (.and
        (.and
          (.eq (.var (Sum.inl AuthorIndex.name) (.varchar 100))
               (.var (Sum.inr (Sum.inl BookIndex.author)) (.varchar 100)))
          (.eq (.var (Sum.inr (Sum.inr ReadingListIndex.bookTitle)) (.varchar 200))
               (.var (Sum.inr (Sum.inl BookIndex.title)) (.varchar 200))))
        (.var (Sum.inl AuthorIndex.retired) .bool))
      (.join (.all authorTable) (.join (.all bookTable) (.all listTable)))
  printFlatSql "  three-way join, nested right" (SQL.Select.fromQuery rightNested).toString
  printSorted <| (← DBMonad.lookup rightNested).map fun row =>
    s!"    {row.value (Sum.inl AuthorIndex.name)}: " ++
    s!"{row.value (Sum.inr (Sum.inl BookIndex.title))} " ++
    s!"at position {row.value (Sum.inr (Sum.inr ReadingListIndex.order))}"
  -- A left join whose left-hand side is a join. The books with no entry in the reading list still
  -- come back, with `NULL` throughout the reading-list columns.
  let leftJoinOverJoin : Query (%database mydb) _ :=
    .leftJoin
      (.filter
        (.eq (.var (Sum.inl AuthorIndex.name) (.varchar 100))
             (.var (Sum.inr BookIndex.author) (.varchar 100)))
        (.join (.all authorTable) (.all bookTable)))
      (.all listTable)
      (.eq (.var (Sum.inr ReadingListIndex.bookTitle) (.varchar 200))
           (.var (Sum.inl (Sum.inr BookIndex.title)) (.varchar 200)))
  printFlatSql "  left join over a join" (SQL.Select.fromQuery leftJoinOverJoin).toString
  printSorted <| (← DBMonad.lookup leftJoinOverJoin).map fun row =>
    s!"    {row.value (Sum.inl (Sum.inr BookIndex.title))} " ++
    s!"at position {row.value (Sum.inr ReadingListIndex.order)}"
  -- A left join whose right-hand side computes a column of its own. Every right-hand column has to
  -- come back `NULL` for a left row that finds no partner, and a computed one is no exception —
  -- but an expression left in the join's own `SELECT` list is evaluated per row of the join, so an
  -- unmatched row would carry its value (here `1`) rather than `NULL`. The right-hand side
  -- therefore becomes a subquery, whose columns the join nulls out like any other's.
  let flagged : Query (%database mydb) _ :=
    .leftJoin (.all bookTable)
      (.extend "onTheList" { type := .int, nullable := false } (.int 1) (.all listTable))
      (.eq (.var (Sum.inl BookIndex.title) (.varchar 200))
           (.var (Sum.inr (Sum.inl ReadingListIndex.bookTitle)) (.varchar 200)))
  printAliasedSql "  left join over a computed right side" (SQL.Select.fromQuery flagged).toString
  printSorted <| (← DBMonad.lookup flagged).map fun row =>
    letI flag : Option Int := row.value (Sum.inr (Sum.inr ⟨⟩))
    s!"    {row.value (Sum.inl BookIndex.title)}: on the list {flag}"
  -- The rows the reading list holds are the next demo's to create.
  let _ ← HasModel.delete (α := ReadingList) .true

end JoinExample
