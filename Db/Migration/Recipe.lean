/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Query.Basic
import Db.Utils.MatchMap

universe t u

section

variable {α : Type u} {k : Type t} [Hashable k] [BEq k] [LawfulBEq k] [LawfulHashable k]

def Std.HashMap.IndexType (m : Std.HashMap k α) : Type :=
  Fin m.keys.length
  deriving Hashable, DecidableEq, Repr, Enum

instance (m : Std.HashMap k α) [ToString k] : ToString m.IndexType where
  toString (i : Fin _) := toString m.keys[i]

instance (m : Std.HashMap k α) [FromString k] : FromString m.IndexType where
  fromString s :=
    -- Can't use `Option` monad, because of universe polymorphism
    match (FromString.fromString s : Option k) with
    | some key => List.finIdxOf? key _
    | none => none

attribute [grind .] Std.HashMap.mem_of_mem_keys

theorem List.Nodup.finIdxOf?_getElem {α : Type u} [BEq α] [LawfulBEq α] {l : List α}
    (i : Fin l.length) (h : l.Nodup) : l.finIdxOf? l[i] = i := by
  rw [List.finIdxOf?_eq_some_iff]
  refine ⟨rfl, fun j hj heq => ?_⟩
  suffices j = i by grind
  ext
  apply List.getElem?_inj j.isLt h
  grind

-- TODO: generalise by adding a `LawfulFromToString` class
instance (m : Std.HashMap String α) : Indexing m.IndexType where
  fromString_toString (i : Fin _) := by
    show List.finIdxOf? m.keys[i] _ = _
    exact Std.HashMap.nodup_keys.finIdxOf?_getElem _

end

/--
The minimal data required for defining a table. This is less convenient to work with, because
it does not contain an explicit indexing type. But `Table : Type 1`, which
causes universe issues with monads.
-/
structure TableRecipe : Type where
  columns : Std.HashMap String Column
  deriving Repr, BEq

/--
The minimal data required for defining a database. This is less convenient to work with, because
it does not contain an explicit indexing type. But `Database : Type 1`, which
causes universe issues with monads.
-/
structure DatabaseRecipe : Type where
  tables : Std.HashMap String TableRecipe
  deriving Repr

def TableRecipe.Index (recipe : TableRecipe) : Type :=
  recipe.columns.IndexType
  deriving Indexing

def DatabaseRecipe.Index (recipe : DatabaseRecipe) : Type :=
  recipe.tables.IndexType
  deriving Indexing

/-- A reconstructed table from a table recipe. -/
def TableRecipe.table (recipe : TableRecipe) : Table where
  Index := recipe.Index
  columns (i : Fin _) := recipe.columns[recipe.columns.keys[i]]'(by grind)

/-- A reconstructed database from a database recipe. -/
def DatabaseRecipe.table (recipe : DatabaseRecipe) : Database where
  Index := recipe.Index
  tables (i : Fin _) :=
    recipe.tables[recipe.tables.keys[i]]'(by grind) |>.table

def Table.recipe (table : Table) : TableRecipe where
  columns := .ofArray <|
    (Enum.all table.Index).map fun idx => (toString idx, table.columns idx)

def Database.recipe (database : Database) : DatabaseRecipe where
  tables := .ofArray <|
    (Enum.all database.Index).map fun idx => (toString idx, database.tables idx |>.recipe)

instance : EmptyCollection DatabaseRecipe where
  emptyCollection := { tables := ∅ }

@[simp, grind =]
theorem DatabaseRecipe.tables_empty : (∅ : DatabaseRecipe).tables = ∅ := rfl

-- maybe better for computations?
structure Recipe : Type where
  columns : Std.HashMap (String × String) Column
  deriving Repr

@[grind]
def TableRecipe.names (recipe : TableRecipe) : Std.HashSet String :=
  .mk <| recipe.columns.map fun _ _ => ()

abbrev ColumnOperation : Type :=
  Column

instance : HasOperations Column ColumnOperation where
  isValid _ _ := true
  execute _ op _ := op
  operations _ target := #[target]

abbrev TableOperation : Type :=
  Std.HashMap.Operation String Column ColumnOperation

@[grind]
instance : HasOperations TableRecipe TableOperation where
  isValid table op :=
    HasExecution.isValid table.columns op
  execute recipe op valid :=
    { columns := HasExecution.execute recipe.columns op valid }
  operations source target := HasOperations.operations source.columns target.columns

abbrev DatabaseOperation : Type :=
  Std.HashMap.Operation String TableRecipe TableOperation

@[grind]
instance : HasOperations DatabaseRecipe DatabaseOperation where
  isValid database op :=
    HasExecution.isValid database.tables op
  execute recipe op valid :=
    { tables := HasExecution.execute recipe.tables op valid }
  operations source target := HasOperations.operations source.tables target.tables


@[simp, grind =]
theorem DatabaseOperation.isValid_iff (d : DatabaseRecipe) (op : DatabaseOperation) :
    HasExecution.isValid d op = op.isValid d.tables :=
  rfl

def TableRecipe.operations (source target : TableRecipe) :
    Array TableOperation :=
  HasOperations.operations source target

def DatabaseRecipe.operations (source target : DatabaseRecipe) :
    Array DatabaseOperation :=
  HasOperations.operations source target
