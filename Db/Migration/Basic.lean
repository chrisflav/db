/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Query.Basic
import Db.Utils.Equiv

structure Indexing.Map {α β : Type} [Indexing α] [Indexing β] (f : α → β) : Prop where
  toString_apply (a : α) : ToString.toString (f a) = ToString.toString a

structure Indexing.Equiv (α β : Type) [Indexing α] [Indexing β] extends α ≃ β where
  indexing_toFun : Indexing.Map toFun

@[ext]
def Indexing.Equiv.ext {α β : Type} [Indexing α] [Indexing β]
    {e₁ e₂ : Indexing.Equiv α β} (h : e₁.toFun = e₂.toFun) :
    e₁ = e₂ := by
  cases e₁
  cases e₂
  simp only [mk.injEq]
  ext1
  exact h

@[simp]
theorem Indexing.Equiv.toString_toFun {α β : Type} [Indexing α] [Indexing β]
    (e : Indexing.Equiv α β) (a : α) :
    ToString.toString (e.toFun a) = ToString.toString a :=
  e.indexing_toFun.toString_apply _

@[simp]
theorem Indexing.Equiv.toString_invFun {α β : Type} [Indexing α] [Indexing β]
    (e : Indexing.Equiv α β) (b : β) :
    ToString.toString (e.invFun b) = ToString.toString b := by
  rw [← e.toFun_invFun b, toString_toFun, e.toFun_invFun]

section

variable (α β : Type) [Indexing α] [Indexing β]

instance (α β : Type) [Indexing α] [Indexing β] : Subsingleton (Indexing.Equiv α β) where
  allEq x y := by
    ext a
    apply Indexing.injective_toString
    simp

theorem Indexing.Equiv.nonempty_iff :
    Nonempty (Indexing.Equiv α β) ↔
      ((Enum.all α).toList.map ToString.toString).Perm
        ((Enum.all β).toList.map ToString.toString) := by
  sorry

instance : Decidable (Nonempty (Indexing.Equiv α β)) :=
  decidable_of_decidable_of_iff (Indexing.Equiv.nonempty_iff _ _).symm

end

structure Table.Migration (source target : Table) where
  map : source.Index → Option target.Index

inductive Table.MigrationStep' (source target : Table) where
  | dropColumn (index : source.Index)
  | addColumn (index : target.Index)
  | alterColumn (old : source.Index) (new : target.Index)

def Table.Migration.steps {source target : Table} (migration : source.Migration target) :
    List (source.MigrationStep' target) := Id.run <| do
  let mut ops := []
  let mut visited : Std.HashSet target.Index := .emptyWithCapacity
  for index in Enum.all source.Index do
    match migration.map index with
    | some val =>
      visited := visited.insert val
      ops := .alterColumn index val :: ops
    | none => ops := .dropColumn index :: ops
  for index in Enum.all target.Index do
    if index ∈ visited then
      continue
    ops := .addColumn index :: ops
  return ops

def Table.columnOfString (table : Table) (s : String) : Option Column := do
  return table.columns (← FromString.fromString s)

def Table.Equivalent (source target : Table) : Prop :=
  ∃ (e : Indexing.Equiv source.Index target.Index),
    ∀ i, target.columns (e.toFun i) = source.columns i

theorem Table.Equivalent.iff (source target : Table) :
    source.Equivalent target ↔
      Nonempty (Indexing.Equiv source.Index target.Index) ∧
        (Enum.all source.Index).all fun idx ↦
          source.columnOfString (ToString.toString idx) ==
            target.columnOfString (ToString.toString idx) :=
  sorry

instance (source target : Table) : Decidable (Table.Equivalent source target) :=
  decidable_of_decidable_of_iff (Table.Equivalent.iff source target).symm

/--
A migration from database stage `source` to database stage `target`
is a recipe how to turn data in `source` into data in `target`.
-/
structure Database.Migration (source target : Database) where
  map : source.Index → target.Index
  indexing : Indexing.Map map
  entry (i : source.Index) (e : (Table.view i).Entry) :
    (Table.view (map i)).Entry

inductive Column.MigrationStep (column : Column) where

inductive Table.MigrationStep (table : Table) where
  | addColumn (column : Column) (name : String)
  | modifyColumn (column : Column) (step : column.MigrationStep)
  | dropColumn (name : table.Index)
  | reindex (T : Type) [Indexing T] (e : table.Index ≃ T)

inductive Database.MigrationStep (database : Database) where
  | createTable (table : Table) (name : String)
  | modifyTable (table : Table) (step : table.MigrationStep)
  | dropTable (name : database.Index)
  | reindex (T : Type) [Indexing T] (e : database.Index ≃ T)

def Table.addColumn (table : Table) (name : String) (col : Column) : Table :=
  haveI : Disjoint table.Index (IUnit name) := sorry
  { Index := table.Index ⊕ IUnit name
    indexing := .sumOfDisjoint _ _
    columns := Sum.elim table.columns fun _ ↦ col }

def Table.MigrationStep.result {table : Table} : table.MigrationStep → Table
  | reindex T e =>
    { Index := T
      columns := table.columns ∘ e.invFun }
  | addColumn col name => table.addColumn name col
  | _ => sorry
