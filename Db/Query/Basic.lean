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

attribute [reducible, instance] Indexing.toString Indexing.fromString Indexing.decidableEq
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

@[reducible] def Indexing.sumOfDisjoint (α β : Type) [Indexing α] [Indexing β] [Disjoint α β] :
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

@[reducible] def Indexing.sum (α β : Type) [Indexing α] [Indexing β] : Indexing (α ⊕ β) where
  length := Enum.length α + Enum.length β
  encoding :=
    (Equiv.sumCongr Enum.encoding Enum.encoding).trans finSumFinEquiv
  toString.toString :=
    Sum.elim (fun a => s!"left__{ToString.toString a}")
      (fun a => s!"right__{ToString.toString a}")
  fromString.fromString s := do
    if let some suffix := s.stripPrefix? "left__" then
      let a : α ← FromString.fromString suffix
      return .inl a
    else if let some suffix := s.stripPrefix? "right__" then
      let a : β ← FromString.fromString suffix
      return .inr a
    else
      none
  hash :=
    -- this is probably bad?
    Sum.elim hash hash
  fromString_toString x := by
    obtain (a | b) := x
    · simp [Indexing.fromString_toString]
    · have hne : ∀ r : String, "right__" ++ ToString.toString b ≠ "left__" ++ r := by
        intro r h
        have hl := congrArg String.toList h
        rw [String.toList_append, String.toList_append] at hl
        simp only [show "right__".toList = ['r', 'i', 'g', 'h', 't', '_', '_'] from by decide,
          show "left__".toList = ['l', 'e', 'f', 't', '_', '_'] from by decide] at hl
        simp at hl
      simp [String.stripPrefix?_eq_none hne, Indexing.fromString_toString]

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
  /-- A value a query computes rather than reads from a table, such as an aggregate. It carries a
  full `Column` rather than a `DBType`, because such a value can be `NULL` even when no column it
  is computed from is nullable. -/
  | computation (n : String) (c : Column) : Name d
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

def Database.Name.column {d : Database} : d.Name → Column
  | .ident i => i.column
  | .computation _ c => c

def Database.Name.dbtype {d : Database} : d.Name → DBType
  | .ident i => i.dbtype
  | .computation _ c => c.type

def Database.Name.toString {d : Database} : d.Name → String
  | .ident i => i.toString
  | .computation s _ => s

@[ext]
structure View.Entry {d : Database} (view : View d) : Type where
  value (idx : view.Index) : (view.name idx).column.Value

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

/-- Whether values of a type are character data, and hence comparable with SQL's `LIKE`. -/
def DBType.isTextLike : DBType → Bool
  | .varchar _ => true
  | _ => false

/-- The direction of one `ORDER BY` key. -/
inductive SortDirection where
  | asc
  | desc
  deriving DecidableEq, Repr

/-- One `ORDER BY` key: a column of the view, and the direction to sort it in.

Sorting is by column rather than by arbitrary expression; that is what the backends need and it
keeps the key independent of `DBExpr`. -/
structure SortKey {d : Database} (view : View d) where
  column : view.Index
  direction : SortDirection := .asc

/-- An aggregate function of one column.

`AVG` is missing because `DBType` has no floating-point type to give its result. -/
inductive AggregateFn where
  | count
  | countDistinct
  | sum
  | min
  | max
  deriving DecidableEq, Repr

/-- The name under which an aggregate function is applied in SQL. -/
def AggregateFn.toString : AggregateFn → String
  | .count | .countDistinct => "COUNT"
  | .sum => "SUM"
  | .min => "MIN"
  | .max => "MAX"

/-- Whether the aggregate applies to the distinct values of its column. -/
def AggregateFn.distinct : AggregateFn → Bool
  | .countDistinct => true
  | _ => false

/-- Whether the function is defined on values of this type. Counting works on anything, `SUM` only
on numbers, and `MIN`/`MAX` on everything the databases order, which excludes booleans. -/
def AggregateFn.appliesTo : AggregateFn → DBType → Bool
  | .count, _ => true
  | .countDistinct, _ => true
  | .sum, t => t == .int
  | .min, t => t != .bool
  | .max, t => t != .bool

/-- How one output column of an aggregate query is computed from the columns of its source. -/
inductive AggregateEntry {d : Database} (source : View d) : Type where
  /-- A column that is grouped over. It is selected as is and appears in `GROUP BY`. -/
  | group (col : source.Index)
  /-- `COUNT(*)`, the number of rows in the group. -/
  | countAll
  /-- An aggregate function applied to one column, which has to be defined on that column's
  type. -/
  | apply (f : AggregateFn) (col : source.Index)
      (h : f.appliesTo (source.name col).dbtype := by rfl)

/-- The column an entry computes, including whether its value can be `NULL`. -/
def AggregateEntry.column {d : Database} {source : View d} : AggregateEntry source → Column
  | .group col => (source.name col).column
  | .countAll => { type := .int, nullable := false }
  | .apply .count _ _ => { type := .int, nullable := false }
  | .apply .countDistinct _ _ => { type := .int, nullable := false }
  -- `SUM`, `MIN` and `MAX` are `NULL` for a group in which every value is `NULL`, whatever the
  -- column they are applied to.
  | .apply _ col _ => { type := (source.name col).dbtype, nullable := true }

/-- The columns of `source` that an aggregation groups over, i.e. those its output selects
unaggregated. -/
def AggregateEntry.groupColumn {d : Database} {source : View d} :
    AggregateEntry source → Option source.Index
  | .group col => some col
  | _ => none

/--
An aggregation of the rows of `source` into the columns of `out`: every column of `out` is either
one of the columns of `source` that is grouped over, or an aggregate function of the rows of a
group.

The `out` view is supplied by the caller, which is what keeps this general: its columns are
typically `Database.Name.computation` names, whose type has to agree with what the corresponding
entry computes.
-/
structure Aggregation {d : Database} (source out : View d) where
  /-- What each output column is computed from. -/
  entry : out.Index → AggregateEntry source
  /-- Each output column is declared exactly as its entry computes it. This is an equality of
  `Column`s rather than of `DBType`s: getting the nullability wrong would make the backend read a
  `NULL` into a type that has no value for it. -/
  column_entry : ∀ i, (entry i).column = (out.name i).column := by
    intro i; first | rfl | (cases i <;> rfl)

/-- The columns that are grouped over, in the order of the output view. -/
def Aggregation.groupColumns {d : Database} {source out : View d} (a : Aggregation source out) :
    List source.Index :=
  (Enum.all out.Index).toList.filterMap fun i => (a.entry i).groupColumn

mutual

/--
A typed expression over the columns of `view`.

A `DBExpr` is pure syntax: it carries no semantics of its own and is translated to SQL by the
backends. In particular SQL's three-valued logic is not modelled here; `NULL` propagates through
the comparisons exactly as the target database defines it, which is why `isNull` rather than
`eq _ (null _)` is the way to test for `NULL`.
-/
inductive DBExpr (d : Database) : View d → DBType → Type 1 where
  /-- The literal `TRUE`. -/
  | true {view : View d} : DBExpr d view .bool
  /-- The literal `FALSE`. -/
  | false {view : View d} : DBExpr d view .bool
  /-- Conjunction, `AND`. -/
  | and {view : View d} (e₁ e₂ : DBExpr d view .bool) : DBExpr d view .bool
  /-- Disjunction, `OR`. -/
  | or {view : View d} (e₁ e₂ : DBExpr d view .bool) : DBExpr d view .bool
  /-- Negation, `NOT`. -/
  | not {view : View d} (e : DBExpr d view .bool) : DBExpr d view .bool
  /-- Equality, `=`. -/
  | eq {view : View d} {t : DBType} (e₁ e₂ : DBExpr d view t) : DBExpr d view .bool
  /-- Disequality, `<>`. -/
  | ne {view : View d} {t : DBType} (e₁ e₂ : DBExpr d view t) : DBExpr d view .bool
  /-- Strictly less than, `<`. -/
  | lt {view : View d} {t : DBType} (e₁ e₂ : DBExpr d view t) : DBExpr d view .bool
  /-- Less than or equal, `<=`. -/
  | le {view : View d} {t : DBType} (e₁ e₂ : DBExpr d view t) : DBExpr d view .bool
  /-- Strictly greater than, `>`. -/
  | gt {view : View d} {t : DBType} (e₁ e₂ : DBExpr d view t) : DBExpr d view .bool
  /-- Greater than or equal, `>=`. -/
  | ge {view : View d} {t : DBType} (e₁ e₂ : DBExpr d view t) : DBExpr d view .bool
  /-- `IS NULL`. -/
  | isNull {view : View d} {t : DBType} (e : DBExpr d view t) : DBExpr d view .bool
  /-- `IS NOT NULL`. -/
  | isNotNull {view : View d} {t : DBType} (e : DBExpr d view t) : DBExpr d view .bool
  /-- Pattern match, `LIKE`. In the pattern, `%` and `_` are wildcards and `\` escapes the
  character after it, including itself; a literal backslash is therefore written `\\`. This is
  declared to the backend as `ESCAPE '\'`, since PostgreSQL and SQLite disagree on the default.
  `DBExpr.likeEscape` escapes a string to be matched literally. -/
  | like {view : View d} {t : DBType} (e : DBExpr d view t) (pattern : String)
      (h : t.isTextLike := by rfl) : DBExpr d view .bool
  /-- Membership in a literal list of values, `IN (v₁, ..., vₙ)`. An empty list is `FALSE`. -/
  | inList {view : View d} {t : DBType} (e : DBExpr d view t) (values : List t.Value) :
      DBExpr d view .bool
  /-- Membership in the `col` column of a subquery, `IN (SELECT col FROM ...)`. The column has to
  have the same type as `e`, which for a literal index is checked by the default `rfl`. -/
  | inSubquery {view sub : View d} {t : DBType} (e : DBExpr d view t) (q : Query d sub)
      (col : sub.Index) (h : (sub.name col).dbtype = t := by rfl) : DBExpr d view .bool
  /-- The column named by `i`. Its `DBType` has to be the one the view assigns to `i`, which for a
  literal index is checked by the default `rfl`. -/
  | var {view : View d} (i : view.Index) (t : DBType)
      (h : (view.name i).dbtype = t := by rfl) : DBExpr d view t
  /-- A string literal. -/
  | str {view : View d} {n : Nat} (s : VarChar n) : DBExpr d view (.varchar n)
  /-- An integer literal. -/
  | int {view : View d} (n : Int) : DBExpr d view .int
  /-- The literal `NULL`, at a given type. -/
  | null {view : View d} (t : DBType) : DBExpr d view t

/--
A query on the database `d` indexed over the (unique) names of the outputs.
-/
inductive Query (d : Database) : View d → Type 1 where
  /-- All rows of a table. -/
  | all (table : d.Index) : Query d (Table.view table)
  /-- Filter a query by a condition. -/
  | filter {view : View d} (e : DBExpr d view .bool) (q : Query d view) : Query d view
  /--
  Cross join (cartesian product). All other join operations can be obtained combining this
  with the appropriate filter condition.
  -/
  | join {s t : View d} (q₁ : Query d s) (q₂ : Query d t) : Query d (s.prod t)
  -- Example: `Query d (s.prod t) -> Query d s`
  | project {s t : View d} (p : t.Hom s) (q₁ : Query d s) : Query d t
  /-- Sort the rows of a query. Sorting is view-preserving: the output columns are unchanged. -/
  | orderBy {view : View d} (keys : List (SortKey view)) (q : Query d view) : Query d view
  /-- Keep at most `n` rows. -/
  | limit {view : View d} (n : Nat) (q : Query d view) : Query d view
  /-- Skip the first `n` rows. -/
  | offset {view : View d} (n : Nat) (q : Query d view) : Query d view
  /-- Group the rows of `q` and aggregate each group into a row of `out`. -/
  | aggregate {source out : View d} (a : Aggregation source out) (q : Query d source) : Query d out

end

/-- Escape the SQL `LIKE` wildcards `%` and `_` in `s`, as well as the escape character `\`
itself, so that a pattern built from it matches `s` literally. -/
def DBExpr.likeEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "%" "\\%" |>.replace "_" "\\_"

/-- `e LIKE '%s%'`, matching rows in which `s` occurs as a substring. -/
def DBExpr.contains {d : Database} {view : View d} {t : DBType} (e : DBExpr d view t) (s : String)
    (h : t.isTextLike := by rfl) : DBExpr d view .bool :=
  .like e s!"%{DBExpr.likeEscape s}%" h

-- The `isTextLike` side condition has to be dischargeable when the length of the column is not a
-- literal, so that helpers over `like` can be length-polymorphic.
example {d : Database} {n : Nat} {view : View d} (e : DBExpr d view (.varchar n)) :
    DBExpr d view .bool :=
  .like e "abc%"

example {d : Database} {n : Nat} {view : View d} (e : DBExpr d view (.varchar n)) :
    DBExpr d view .bool :=
  .contains e "abc"

/-- The one-column view holding a computed value under the name `name`. -/
def View.singleton (d : Database) (name : String) (c : Column) : View d where
  Index := IUnit name
  name _ := .computation name c

/-- `SELECT COUNT(*)`: the number of rows of `q`, as a query with a single `int` column named
`name`. -/
def Query.countAll {d : Database} {view : View d} (q : Query d view) (name : String := "count") :
    Query d (View.singleton d name { type := .int, nullable := false }) :=
  .aggregate { entry _ := .countAll } q

/-- The single value of a row of a query over `View.singleton`. -/
def View.singletonValue {d : Database} {name : String} {c : Column}
    (e : (View.singleton d name c).Entry) : c.Value :=
  e.value ⟨⟩

def signature {d : Database} (s : Std.HashSet d.Name) : Std.HashMap d.Name DBType :=
  s.inner.map (fun n _ ↦ n.dbtype)

structure Database.Insert (d : Database) (tableName : d.Index) where
  entry : (Table.view tableName).Entry
