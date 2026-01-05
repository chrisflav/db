/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Std

universe v t u

variable {k : Type t} {α : Type t} [BEq k] [Hashable k] [LawfulBEq k]

class HasOperations (α : Type u) (op : α → Type t) where
  execute (init : α) (operation : op init) : α
  operations (source target : α) : Array (op source)

/-- An operation on a `HashMap`. -/
inductive Std.HashMap.Operation (op : α → Type v) [∀ a, Repr (op a)] (m : Std.HashMap k α) where
  /-- Insert a new entry with a not yet existing key. -/
  | insert (new : k) (value : α) (notMem : new ∉ m := by grind)
  /-- Remove an existing entry. -/
  | remove (key : k) (mem : key ∈ m := by grind)
  /-- Replace the value of an existing entry. -/
  | alter (key : k) (mem : key ∈ m := by grind) (operation : op m[key])
  /-- Rename the key of an existing entry. -/
  | rename (old new : k) (mem : old ∈ m := by grind) (notMem : new ∉ m := by grind)
  deriving Repr

def Std.HashMap.Operation.cost {m : Std.HashMap k α} {op : α → Type v} [∀ a, Repr (op a)] :
    m.Operation op → Nat
  | .insert _ _ _ => 2
  | .remove _ _ => 7
  | .rename _ _ _ _ => 1
  | .alter _ _ _ => 5

variable {op : α → Type t} [∀ a, Repr (op a)] [HasOperations α op]

def Std.HashMap.Operation.result {m : Std.HashMap k α} :
    m.Operation op → Std.HashMap k α
  | .insert new value _ => m.insert new value
  | .rename old new _ _ => (m.insert new m[old]).erase old
  | .alter key _ operation => m.insert key <| HasOperations.execute _ operation
  | .remove key _ => m.erase key

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
def Std.HashMap.operations [BEq α] (source target : Std.HashMap k α) :
    Array (source.Operation op) := Id.run do
  let mut ops : Array (source.Operation op) := #[]
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
          ops := ops.push (.alter key (by grind) valOp)

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

instance [BEq α] : HasOperations (Std.HashMap k α) (Std.HashMap.Operation op) where
  execute _ operation := operation.result
  operations source target := source.operations target
