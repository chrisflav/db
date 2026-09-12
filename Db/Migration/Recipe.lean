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
  apply (List.getElem?_inj j.isLt h).mp
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
  /-- The names of the primary key columns, in order. Empty for a table without one. -/
  primaryKey : List String := []
  /-- The groups of column names that have to be unique together. -/
  unique : List (List String) := []
  /-- The foreign keys of the table. -/
  foreignKeys : List (ForeignKey String) := []
  /-- The indexes of the table. Not part of `normalizedConstraints`: an index change is migrated
  rather than reported, since `CREATE INDEX`/`DROP INDEX` says the whole of it. -/
  indexes : List (TableIndex String) := []
  deriving Repr

/--
The constraints of a table in a normal form.

A `UNIQUE` group and the list of groups and of foreign keys have no meaningful order, and a
database does not report them in the order the table declared them, so they are compared sorted.
The primary key does keep its order, which is part of what it means.
-/
def TableRecipe.normalizedConstraints (recipe : TableRecipe) :
    List String × List String × List String :=
  (recipe.primaryKey,
   (recipe.unique.map fun group =>
      ", ".intercalate (group.mergeSort fun a b => decide (a ≤ b))).mergeSort
        (fun a b => decide (a ≤ b)),
   (recipe.foreignKeys.map fun fk =>
      s!"({", ".intercalate fk.columns}) -> {fk.foreignTable}" ++
        s!"({", ".intercalate fk.foreignColumns}) " ++
        s!"ON DELETE {fk.onDelete.sql} ON UPDATE {fk.onUpdate.sql}").mergeSort
          (fun a b => decide (a ≤ b)))

instance : BEq TableRecipe where
  beq s t := s.columns == t.columns && s.normalizedConstraints == t.normalizedConstraints

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

/-- A reconstructed table from a table recipe. A constraint naming a column the recipe does not
have is dropped, there being no index to name it by. -/
def TableRecipe.table (recipe : TableRecipe) : Table where
  Index := recipe.Index
  columns (i : Fin _) := recipe.columns[recipe.columns.keys[i]]'(by grind)
  primaryKey := recipe.primaryKey.filterMap FromString.fromString
  unique := recipe.unique.map fun group => group.filterMap FromString.fromString
  foreignKeys := recipe.foreignKeys.filterMap fun fk => do
    let columns ← fk.columns.mapM FromString.fromString
    return { columns := columns
             foreignTable := fk.foreignTable
             foreignColumns := fk.foreignColumns
             onDelete := fk.onDelete
             onUpdate := fk.onUpdate }
  indexes := recipe.indexes.filterMap fun idx => do
    let keys ← idx.keys.mapM fun k => do
      let column ← FromString.fromString k.column
      return { column := column, direction := k.direction, collation := k.collation }
    return { name := idx.name, keys := keys, unique := idx.unique }

/-- A reconstructed database from a database recipe. -/
def DatabaseRecipe.table (recipe : DatabaseRecipe) : Database where
  Index := recipe.Index
  tables (i : Fin _) :=
    recipe.tables[recipe.tables.keys[i]]'(by grind) |>.table

def Table.recipe (table : Table) : TableRecipe where
  columns := .ofArray <|
    (Enum.all table.Index).map fun idx => (toString idx, table.columns idx)
  primaryKey := table.primaryKey.map toString
  unique := table.unique.map fun group => group.map toString
  foreignKeys := table.foreignKeys.map (ForeignKey.map toString)
  indexes := table.indexes.map (TableIndex.map toString)

def Database.recipe (database : Database) : DatabaseRecipe where
  tables := .ofArray <|
    (Enum.all database.Index).map fun idx => (toString idx, database.tables idx |>.recipe)

instance : Coe Database DatabaseRecipe where
  coe d := d.recipe

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
    { recipe with columns := HasExecution.execute recipe.columns op valid }
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

/--
Order `names` so that each comes after the names `dependsOn` gives for it, as far as that is
possible. A name that depends on itself, or on one that is not in `names`, is unconstrained by that
dependency; a cycle among the names cannot be ordered and is left in the order it came.
-/
private def dependencyOrder (dependsOn : String → List String) (names : Array String) :
    Array String := Id.run do
  let mut placed : Std.HashSet String := ∅
  let mut res : Array String := #[]
  let mut remaining := names.toList
  -- Each pass places at least one name unless none can be placed, so `names.size` passes suffice.
  for _ in [0:names.size] do
    if remaining.isEmpty then
      break
    let mut next : List String := []
    for name in remaining do
      let ready := (dependsOn name).all fun d =>
        d == name || !(names.contains d) || placed.contains d
      if ready then
        res := res.push name
        placed := placed.insert name
      else
        next := next ++ [name]
    if next.length == remaining.length then
      break
    remaining := next
  return res ++ remaining.toArray

def DatabaseRecipe.operations (source target : DatabaseRecipe) :
    Array DatabaseOperation :=
  letI ops := HasOperations.operations source target
  letI inserts := ops.filterMap fun op =>
    match op with
    | .insert name recipe => some (name, recipe)
    | _ => none
  letI removes := ops.filterMap fun op =>
    match op with
    | .remove name => some name
    | _ => none
  letI others := ops.filter fun op =>
    match op with
    | .insert .. => false
    | .remove .. => false
    | _ => true
  letI references (recipe : TableRecipe) : List String :=
    recipe.foreignKeys.map (·.foreignTable)
  -- A `CREATE TABLE` carrying `REFERENCES` fails unless its target already exists, and a
  -- `DROP TABLE` fails while something still references it, so creations go in dependency order
  -- and drops in the reverse.
  letI createOrder := dependencyOrder
    (fun name => ((inserts.find? (·.1 == name)).map fun t => references t.2).getD [])
    (inserts.map (·.1))
  letI dropOrder := dependencyOrder
    (fun name => (source.tables[name]?.map references).getD []) removes
  letI orderedInserts := createOrder.filterMap fun name =>
    (inserts.find? (·.1 == name)).map fun t => Std.HashMap.Operation.insert t.1 t.2
  letI orderedRemoves := dropOrder.reverse.map Std.HashMap.Operation.remove
  others ++ orderedRemoves ++ orderedInserts

/-- The same recipe with the indexes of one table replaced.

This is where indexes are attached to a schema built by the model layer: `@[model]` generates a
table without any, because which of a structure's fields are worth an index is not something the
structure says. `tableIndexes` names the columns through the table's own index type, so the
strings this takes are not written by hand:

```lean
def indexedDb : DatabaseRecipe :=
  (%database mydb).recipe.withIndexes "book" <| tableIndexes BookIndex
    [{ name := "idx_book_author", keys := [{ column := .author }] }]
```
-/
def DatabaseRecipe.withIndexes (r : DatabaseRecipe) (table : String)
    (indexes : List (TableIndex String)) : DatabaseRecipe where
  tables := r.tables.map fun name t =>
    if name == table then { t with indexes := indexes } else t

/-- A change to the indexes of a database. -/
inductive IndexOperation where
  | create (table : String) (index : TableIndex String)
  | drop (table : String) (name : String)
  deriving Repr

/-- The index operations that bring `source` to `target`.

Only the index *names* the target declares are managed. A declared index that is missing is
created; one that exists in another shape is dropped and re-created, neither backend being able to
alter an index in place. An index the database has under a name the target does not mention is left
alone: `autoUpdate` is not the only thing that may have created an index, and dropping one it did
not put there is not a migration, it is data loss of the kind that only shows up as a slow query
much later.

Only tables the target declares are considered; one that is about to be dropped takes its indexes
with it. -/
def DatabaseRecipe.indexOperations (source target : DatabaseRecipe) : Array IndexOperation :=
  Id.run do
    let mut res := #[]
    for (name, targetTable) in target.tables.toList do
      let sourceIndexes := (source.tables[name]?.map (·.indexes)).getD []
      for idx in targetTable.indexes do
        match sourceIndexes.find? (·.name == idx.name) with
        | some existing =>
          unless existing == idx do
            -- The name has to be freed before it can be taken again.
            res := res.push (.drop name idx.name)
            res := res.push (.create name idx)
        | none => res := res.push (.create name idx)
    return res

/-- The names of the tables that exist in both schemas but declare different constraints.

The operation language describes column changes only, so a constraint change on an existing table
cannot be migrated; reporting it is what keeps it from being applied silently as a no-op. -/
def DatabaseRecipe.constraintMismatches (source target : DatabaseRecipe) : Array String :=
  Id.run do
    let mut res := #[]
    for (name, targetTable) in target.tables.toList do
      if let some sourceTable := source.tables[name]? then
        unless sourceTable.normalizedConstraints == targetTable.normalizedConstraints do
          res := res.push name
    return res

/-- A recipe for a migration valid for the database configuration `source`. -/
structure MigrationRecipe (source : DatabaseRecipe) where
  operations : Array DatabaseOperation
  isValidArray_operations : HasExecution.isValidArray source operations := by native_decide

/-- Execute the given recipe by applying the operations in order. -/
def MigrationRecipe.execute {source : DatabaseRecipe} (migration : MigrationRecipe source) :
    DatabaseRecipe :=
  HasExecution.executeArray source migration.operations migration.isValidArray_operations

/-- A migration recipe from `source` to `target` is a migration recipe valid for `source`
that turns `source` into `target`. -/
structure MigrationRecipeWithTarget (source target : DatabaseRecipe) extends
    MigrationRecipe source where
  operations_execute_eq_nil : toMigrationRecipe.execute.operations target = #[] := by native_decide
