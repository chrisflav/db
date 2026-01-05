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

-- maybe better for computations?
structure Recipe : Type where
  columns : Std.HashMap (String × String) Column
  deriving Repr

@[grind]
def TableRecipe.names (recipe : TableRecipe) : Std.HashSet String :=
  .mk <| recipe.columns.map fun _ _ => ()

abbrev ColumnOperation : Column → Type :=
  fun _ => Column

instance : HasOperations Column ColumnOperation where
  execute _ op := op
  operations _ target := #[target]

abbrev TableOperation (table : TableRecipe) : Type :=
  table.columns.Operation ColumnOperation

instance : HasOperations TableRecipe TableOperation where
  execute recipe op := { columns := HasOperations.execute recipe.columns op }
  operations source target := HasOperations.operations source.columns target.columns

abbrev DatabaseOperation (database : DatabaseRecipe) : Type :=
  database.tables.Operation TableOperation

instance : HasOperations DatabaseRecipe DatabaseOperation where
  execute recipe op := { tables := HasOperations.execute recipe.tables op }
  operations source target := HasOperations.operations source.tables target.tables

def TableRecipe.operations (source target : TableRecipe) :
    Array (TableOperation source) :=
  HasOperations.operations source target

def DatabaseRecipe.operations (source target : DatabaseRecipe) :
    Array (DatabaseOperation source) :=
  HasOperations.operations source target
