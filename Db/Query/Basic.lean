/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Std
import Db.Utils.VarChar
import Db.Utils.FromString
import Db.Utils.Enum
import Db.Utils.String

class Indexing (α : Type) : Type extends Enum α, Hashable α where
  [decidableEq : DecidableEq α]
  [toString : ToString α]
  [fromString : FromString α]
  fromString_toString (x : α) : FromString.fromString (ToString.toString x) = some x := by
    intro x; induction x <;> rfl

attribute [instance] Indexing.toString Indexing.fromString Indexing.decidableEq
attribute [simp, grind .] Indexing.fromString_toString

theorem Indexing.injective_toString {α : Type} [Indexing α] :
    Function.Injective (ToString.toString (α := α)) := by
  intro a b h
  rw [← Option.some_inj, ← Indexing.fromString_toString, ← Indexing.fromString_toString, h]

structure IUnit (name : String) : Type where
  deriving DecidableEq, Hashable

instance (name : String) : Indexing (IUnit name) where
  toString.toString _ := name
  fromString.fromString s := if s == name then some ⟨⟩ else none
  fromString_toString := by simp
  length := 1
  encoding.toFun _ := 0
  encoding.invFun _ := ⟨⟩
  encoding.invFun_toFun := by grind
  encoding.toFun_invFun := by grind

class Disjoint (α β : Type) [Indexing α] [Indexing β] : Prop where
  ne_toString (a : α) (b : β) : toString a ≠ toString b
  fromString_eq_none_left (a : α) : (FromString.fromString (toString a) : Option β) = none
  fromString_eq_none_right (b : β) : (FromString.fromString (toString b) : Option α) = none

def Indexing.sumOfDisjoint (α β : Type) [Indexing α] [Indexing β] [Disjoint α β] :
    Indexing (α ⊕ β) where
  length := Enum.length α + Enum.length β
  encoding :=
    (Equiv.sumCongr Enum.encoding Enum.encoding).trans finSumFinEquiv
  toString.toString := Sum.elim ToString.toString ToString.toString
  fromString.fromString s :=
    match (FromString.fromString s : Option α) with
    | some x => some (.inl x)
    | none => FromString.fromString s >>= fun b ↦ some (.inr b)
  hash :=
    -- this is probably bad?
    Sum.elim hash hash
  fromString_toString x := by
    obtain (a | b) := x
    · simp
    · simp [Disjoint.fromString_eq_none_right]

def Indexing.sum (α β : Type) [Indexing α] [Indexing β] : Indexing (α ⊕ β) where
  length := Enum.length α + Enum.length β
  encoding :=
    (Equiv.sumCongr Enum.encoding Enum.encoding).trans finSumFinEquiv
  toString.toString :=
    Sum.elim (fun a => s!"left__{ToString.toString a}")
      (fun a => s!"right__{ToString.toString a}")
  fromString.fromString s := do
    if let some suffix := s.dropPrefix? "left__" then
      let a : α ← FromString.fromString suffix.toString
      return .inl a
    else if let some suffix := s.dropPrefix? "right__" then
      let a : β ← FromString.fromString suffix.toString
      return .inr a
    else
      none
  hash :=
    -- this is probably bad?
    Sum.elim hash hash
  fromString_toString x := by
    obtain (a | b) := x
    · simp
    · simp [String.dropPrefix?_append_of_ne]

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

abbrev Column.Value : Column → Type
  | { type := type, nullable := false } => type.Value
  | { type := type, nullable := true } => Option type.Value

instance : (col : Column) → FromString col.Value
  | { type := type, nullable := false } => inferInstanceAs (FromString type.Value)
  | { type := type, nullable := true } =>
    { fromString
        | "" => some none
        | "NULL" => some none
        | s => do
          let val : type.Value ← FromString.fromString s
          return (some val) }

instance : (col : Column) → Inhabited col.Value
  | { type := _, nullable := false } => inferInstance
  | { type := _, nullable := true } => inferInstance

instance : (col : Column) → ToString col.Value
  | { type := _, nullable := false } => inferInstance
  | { type := _, nullable := true } => inferInstance

example : (Column.mk .int false).Value = Int := rfl

structure Table where
  Index : Type
  [indexing : Indexing Index]
  columns : Index → Column

attribute [instance] Table.indexing

@[ext]
structure Table.Entry (table : Table) : Type where
  value (idx : table.Index) : (table.columns idx).Value

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

def Database.Ident.dbtype {d : Database} (i : d.Ident) : DBType :=
  i.column.type

def Database.Ident.toString {d : Database} (i : d.Ident) : String :=
  s!"{i.tableName}__{i.columnName}"

def Database.Ident.all (d : Database) : Array d.Ident := Id.run do
  let mut res := #[]
  for table in Enum.all d.Index do
    for column in Enum.all (d.tables table).Index do
      res := res.push { tableName := table
                        columnName := column }
  return res

inductive Database.Name (d : Database) where
  | ident (i : d.Ident) : Name d
  | computation (n : String) (t : DBType) : Name d
  deriving DecidableEq, Hashable

structure View (d : Database) where
  Index : Type
  [indexing : Indexing Index]
  name : Index → d.Name

attribute [instance] View.indexing

def View.prod {d : Database} (view₁ view₂ : View d) : View d where
  Index := view₁.Index ⊕ view₂.Index
  indexing := .sum _ _
  name := Sum.elim view₁.name view₂.name

structure View.Hom {d : Database} (view₁ view₂ : View d) where
  map : view₁.Index → view₂.Index
  name_map (idx : view₁.Index) : view₂.name (map idx) = view₁.name idx

attribute [simp] View.Hom.name_map

def View.Hom.id {d : Database} (view : View d) : Hom view view where
  map i := i
  name_map _ := rfl

def View.Hom.comp {d : Database} {view₁ view₂ view₃ : View d} (f : view₁.Hom view₂)
    (g : view₂.Hom view₃) : Hom view₁ view₃ where
  map := g.map ∘ f.map
  name_map _ := by simp

def View.sumInl {d : Database} (view₁ view₂ : View d) : Hom view₁ (view₁.prod view₂) where
  map := Sum.inl
  name_map _ := rfl

def View.sumInr {d : Database} (view₁ view₂ : View d) : Hom view₂ (view₁.prod view₂) where
  map := Sum.inr
  name_map _ := rfl

inductive DBExpr {d : Database} (view : View d) : DBType → Type 1 where
  | true : DBExpr view .bool
  | false : DBExpr view .bool
  | and (e₁ e₂ : DBExpr view .bool) : DBExpr view .bool
  | eq {t : DBType} (e₁ e₂ : DBExpr view t) : DBExpr view .bool
  | var (i : view.Index) (t : DBType) : DBExpr view t
  | str {n : Nat} (s : VarChar n) : DBExpr view (.varchar n)

def Database.Name.column {d : Database} : d.Name → Column
  | .ident i => i.column
  | .computation _ t =>
    { type := t
      nullable := false }

@[ext]
structure View.Entry {d : Database} (view : View d) : Type where
  value (idx : view.Index) : (view.name idx).column.Value

def Database.Name.dbtype {d : Database} : d.Name → DBType
  | .ident i => i.dbtype
  | .computation _ t => t

def Database.Name.toString {d : Database} : d.Name → String
  | .ident i => i.toString
  | .computation s _ => s

def Table.names {d : Database} (tname : d.Index) :
    Std.HashSet d.Name :=
  .ofList ((Enum.all (d.tables tname).Index).toList.map
    fun i ↦ .ident ⟨tname, i, (d.tables tname).columns i, rfl⟩)

def Table.view {d : Database} (tableName : d.Index) : View d where
  Index := (d.tables tableName).Index
  name colName := .ident { tableName := tableName
                           columnName := colName }

-- TODO: add simp lemmas
def Table.entryViewEquiv {d : Database} (tableName : d.Index) :
    (Table.view tableName).Entry ≃ (d.tables tableName).Entry where
  toFun e := { value idx := e.value idx }
  invFun e := { value idx := e.value idx }

/--
A query on the database `d` indexed over the (unique) names of the outputs.
-/
inductive Query (d : Database) : View d → Type 1 where
  /-- All rows of a table. -/
  | all (table : d.Index) : Query d (Table.view table)
  /-- Filter a query by a condition. -/
  | filter {view : View d} (e : DBExpr view .bool) (q : Query d view) : Query d view
  /--
  Cross join (cartesian product). All other join operations can be obtained combining this
  with the appropriate filter condition.
  -/
  | join {s t : View d} (q₁ : Query d s) (q₂ : Query d t) : Query d (s.prod t)
  -- Example: `Query d (s.prod t) -> Query d s`
  | project {s t : View d} (p : t.Hom s) (q₁ : Query d s) : Query d t

def signature {d : Database} (s : Std.HashSet d.Name) : Std.HashMap d.Name DBType :=
  s.inner.map (fun n _ ↦ n.dbtype)

structure Database.Insert (d : Database) (tableName : d.Index) where
  entry : (Table.view tableName).Entry
