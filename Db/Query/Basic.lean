/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Std
import Db.Utils.VarChar
import Db.Utils.FromString

class Indexing (α : Type) : Type where
  [decidableEq : DecidableEq α]
  [hashable : Hashable α]
  [toString : ToString α]
  [fromString : FromString α]
  -- TODO: add axioms?
  all (α) : Std.HashSet α
  fromString_toString (x : α) : FromString.fromString (ToString.toString x) = some x := by grind

attribute [instance] Indexing.decidableEq Indexing.hashable Indexing.toString Indexing.fromString
attribute [simp, grind] Indexing.fromString_toString

structure IUnit (name : String) : Type where
  deriving DecidableEq, Hashable

instance (name : String) : Indexing (IUnit name) where
  toString.toString _ := name
  fromString.fromString s := if s == name then some ⟨⟩ else none
  all := {⟨⟩}
  fromString_toString := by simp

class Disjoint (α β : Type) [Indexing α] [Indexing β] : Prop where
  ne_toString (a : α) (b : β) : toString a ≠ toString b
  fromString_eq_none_left (a : α) : (FromString.fromString (toString a) : Option β) = none
  fromString_eq_none_right (b : β) : (FromString.fromString (toString b) : Option α) = none

instance (α β : Type) [Indexing α] [Indexing β] [Disjoint α β] : Indexing (α ⊕ β) where
  all := sorry
  toString.toString := Sum.elim toString toString
  fromString.fromString s :=
    match (FromString.fromString s : Option α) with
    | some x => some (.inl x)
    | none => FromString.fromString s >>= fun b ↦ some (.inr b)
  hashable.hash :=
    -- this is probably bad?
    Sum.elim hash hash
  fromString_toString x := by
    obtain (a | b) := x
    · simp
    · simp [Disjoint.fromString_eq_none_right]

inductive DBType where
  | bool : DBType
  | int : DBType
  | varchar (n : Nat) : DBType
  deriving BEq, Repr, DecidableEq, Hashable

protected abbrev DBType.Value : DBType → Type
  | .bool => Bool
  | .varchar n => VarChar n
  | .int => Int

instance (t : DBType) : ToString t.Value where
  toString x :=
    match t with
    | .bool => toString x
    | .varchar _ => toString x
    | .int => toString x

instance (t : DBType) : Inhabited t.Value where
  default :=
    match t with
    | .bool => default
    | .varchar _ => ⟨"", by simp⟩
    | .int => default

instance : (t : DBType) → FromString t.Value
  | .bool => inferInstance
  | .int => inferInstance
  | .varchar _ => inferInstance

structure Column where
  type : DBType
  nullable : Bool
  deriving Repr, Hashable, DecidableEq

structure Table where
  Index : Type
  [indexing : Indexing Index]
  columns : Index → Column

attribute [instance] Table.indexing

structure Table.Entry (table : Table) : Type where
  values (c : table.Index) : (table.columns c).type.Value

structure Database where
  Index : Type
  [indexing : Indexing Index]
  tables : Index → Table

attribute [instance] Database.indexing

--@[grind]
--def Table.HasColumn (t : Table) (name : String) : Prop :=
--  name ∈ t.columns

structure Database.Ident (d : Database) where
  tableName : d.Index
  columnName : (d.tables tableName).Index
  column : Column := (d.tables tableName).columns columnName
  column_eq : (d.tables tableName).columns columnName = column := by grind
  deriving DecidableEq, Hashable

def Database.Ident.table {d : Database} (i : d.Ident) : Table :=
  d.tables i.tableName

inductive List.HasElem {α : Type} : List (String × α) → String → Type
  | here (key : String) (x : α) (l : List (String × α)) : HasElem ((key, x) :: l) key
  | there {key : String} {x : α} {l : List (String × α)}
      (h : l.HasElem key) (y : String × α) : HasElem (y :: l) key

def List.HasElem.get {α : Type} {l : List (String × α)} {key : String} :
      l.HasElem key → α
  | here key x l => x
  | there h y => h.get

structure List.HasElem' {α : Type} (l : List (String × α)) (key : String) where
  idx : Fin l.length
  x : α
  h : l[idx] = (key, x)

def List.HasElem'.get {α : Type} (l : List (String × α)) (key : String)
    (h : l.HasElem' key) : α :=
  h.x

abbrev foo : List (String × Nat) := [("foo", 3), ("bar", 5)]

abbrev fooHasElem : foo.HasElem "foo" := by
  repeat constructor

example : fooHasElem.get = 3 := rfl

def Database.Ident.dbtype {d : Database} (i : d.Ident) : DBType :=
  i.column.type

def Database.Ident.toString {d : Database} (i : d.Ident) : String :=
  s!"{i.tableName}.{i.columnName}"

inductive DBExpr (d : Database) : DBType → Type 1 where
  | true : DBExpr d .bool
  | false : DBExpr d .bool
  | and (e₁ e₂ : DBExpr d .bool) : DBExpr d .bool
  | eq {t : DBType} (e₁ e₂ : DBExpr d t) : DBExpr d .bool
  | var (i : d.Ident) (t : DBType) : DBExpr d t
  | str {n : Nat} (s : VarChar n) : DBExpr d (.varchar n)

inductive Database.Name (d : Database) where
  | ident (i : d.Ident) : Name d
  | computation (n : String) (t : DBType) : Name d
  deriving DecidableEq, Hashable

def Database.Name.dbtype {d : Database} : d.Name → DBType
  | .ident i => i.dbtype
  | .computation _ t => t

def Database.Name.toString {d : Database} : d.Name → String
  | .ident i => i.toString
  | .computation s _ => s

def Table.names {d : Database} (tname : d.Index) :
    Std.HashSet d.Name :=
  .ofList ((Indexing.all (d.tables tname).Index).toList.map
    fun i ↦ .ident ⟨tname, i, (d.tables tname).columns i, rfl⟩)

-- TODO: add join operations
/--
A query on the database `d` indexed over the (unique) names of the outputs.
-/
inductive Query (d : Database) : Std.HashSet d.Name → Type 1 where
  | all (table : d.Index) : Query d (Table.names table)
  | filter {s : Std.HashSet d.Name} (q : Query d s) (e : DBExpr d .bool) : Query d s

def signature {d : Database} (s : Std.HashSet d.Name) : Std.HashMap d.Name DBType :=
  s.inner.map (fun n _ ↦ n.dbtype)

structure Database.Insert (d : Database) (tableName : d.Index) where
  entry : (d.tables tableName).Entry
