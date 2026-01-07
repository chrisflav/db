/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Std

universe v t u

variable {k : Type t} {α : Type t} [BEq k] [Hashable k]

class HasExecution (α : Type u) (op : Type t) where
  isValid : α → op → Bool
  execute (init : α) (operation : op) : isValid init operation → α

class HasOperations (α : Type u) (op : Type t) extends HasExecution α op where
  operations (source target : α) : Array op

variable (k α) in
/-- An operation on a `HashMap`. -/
inductive Std.HashMap.Operation (op : Type v) where
  /-- Insert a new entry with a not yet existing key. -/
  | insert (new : k) (value : α)
  /-- Remove an existing entry. -/
  | remove (key : k)
  /-- Replace the value of an existing entry. -/
  | alter (key : k) (operation : op)
  /-- Rename the key of an existing entry. -/
  | rename (old new : k)
  deriving Repr

@[grind]
def Std.HashMap.Operation.isValid {op : Type v} [HasExecution α op] (m : Std.HashMap k α) :
    Operation k α op → Bool
  | .insert new value => new ∉ m
  | .rename old new => old ∈ m ∧ new ∉ m
  | .alter key operation =>
      ∃ (h : key ∈ m), HasExecution.isValid m[key] operation
  | .remove key => key ∈ m

def Std.HashMap.Operation.cost {op : Type v} [HasExecution α op] :
    Operation k α op → Nat
  | .insert _ _ => 2
  | .remove _ => 7
  | .rename _ _ => 1
  | .alter _ _ => 5

variable {op : Type t} [HasOperations α op]

instance : HasExecution (Std.HashMap k α) (Std.HashMap.Operation k α op) where
  isValid m operation := operation.isValid m
  execute m operation isValid := match operation with
    | .insert new value => m.insert new value
    | .rename old new =>
      have : old ∈ m := by grind
      (m.insert new m[old]).erase old
    | .alter key operation =>
      have h : key ∈ m := by grind
      m.insert key (HasExecution.execute m[key] operation <| by grind)
    | .remove key => m.erase key

@[simp, grind =]
theorem Std.HashMap.hasExecutionIsValid_def (m : Std.HashMap k α)
    (op : Std.HashMap.Operation k α op)  :
    HasExecution.isValid m op = op.isValid m :=
  rfl

-- TODO: prove that the result is a chain of valid operations
-- (i.e. one can apply the whole array one by one, preserving validity in every step)
/--
Greedy matching algorithm producing an array of operations that turn `source` into `target`.
Strategy:
1. Alter keys present in both with different values
2. Rename keys (source-only → target-only) when values match (cost 1 vs remove+insert cost 9)
3. Insert remaining target-only keys
4. Remove remaining source-only keys
-/
-- Universes are monomorphized here, otherwise the monadic code fails, because
-- it can only run in one `Id` monad.
def Std.HashMap.operations [LawfulBEq k] [BEq α] (source target : Std.HashMap k α) :
    Array (Operation k α op) := Id.run do
  let mut ops := #[]
  let mut renamedSource : Std.HashSet k := {}
  let mut renamedTarget : Std.HashSet k := {}

  -- First: handle keys in both (alter if values differ)
  for h : key in source.keys do
    if h2 : key ∈ target then
      let sourceVal := source[key]'(by grind)
      let targetVal := target[key]
      if sourceVal != targetVal then
        let valOperations := HasOperations.operations (op := op) sourceVal targetVal
        for valOp in valOperations do
          ops := ops.push (.alter key valOp)

  -- Second: greedy rename optimization
  -- Collect all source-only and target-only keys first to avoid nested loops
  let sourceOnlyKeys := source.keys.filter (· ∉ target)
  let targetOnlyKeys := target.keys.filter (· ∉ source)

  -- Try to match them greedily
  for h : sourceKey in sourceOnlyKeys do
    if h2 : sourceKey ∉ renamedSource then
      let sourceVal := source[sourceKey]'(by grind)

      -- Find a matching target key
      for h3 : targetKey in targetOnlyKeys do
        if h4 : targetKey ∉ renamedTarget then
          let targetVal := target[targetKey]'(by grind)

          if sourceVal == targetVal then
            ops := ops.push (.rename sourceKey targetKey)
            renamedSource := Std.HashSet.insert renamedSource sourceKey
            renamedTarget := Std.HashSet.insert renamedTarget targetKey
            break

  -- Third: insert remaining target keys not yet handled by rename
  for h : targetKey in target.keys do
    if h : targetKey ∉ source then
      if targetKey ∉ renamedTarget then
        let targetVal := target[targetKey]'(by grind)
        ops := ops.push (.insert targetKey targetVal)

  -- Fourth: remove remaining source keys not handled by rename
  for h : sourceKey in source.keys do
    if sourceKey ∉ target then
      if sourceKey ∉ renamedSource then
        ops := ops.push (.remove sourceKey)

  return ops

instance [LawfulBEq k] [BEq α] :
    HasOperations (Std.HashMap k α) (Std.HashMap.Operation k α op) where
  operations source target := source.operations target
