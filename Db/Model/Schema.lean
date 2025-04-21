import Db.Utils.VarChar

/-- Elementary database types. -/
inductive DBType where
  | nat
  | int
  | bool
  | varchar (n : Nat)
  deriving BEq

abbrev DBType.asType : DBType → Type
  | .nat => Nat
  | .int => Int
  | .bool => Bool
  | .varchar n => VarChar n

instance : ToString DBType where
  toString
    | .nat => "nat"
    | .int => "int"
    | .bool => "bool"
    | .varchar n => s!"varchar({n})"

@[ext]
structure SchemaIdent where
  name : String
  deriving BEq

@[ext]
structure ColumnIdent where
  name : String
  deriving BEq

instance : LawfulBEq ColumnIdent where
  eq_of_beq {x y} h := by
    ext
    exact eq_of_beq h
  rfl {x} := beq_self_eq_true' x.name

/-- An extended database type is either an elementary database type, a foreign key
or a many-to-many field. -/
inductive EDBType where
  | elementary (t : DBType)
  | key (n : SchemaIdent)
  | many (n : SchemaIdent)
  deriving BEq

def EDBType.isElementary : EDBType → Bool
  | .elementary _ => true
  | _ => false

@[ext]
structure Column where
  name : String
  underlying : EDBType

instance : BEq Column where
  beq x y := x.name == y.name && x.underlying == y.underlying

@[ext]
structure Schema where
  name : String
  columns : List Column
  keys : List ColumnIdent
  nodup_columns : (columns.map Column.name).Nodup := by decide
  nodup_keys : (keys.map ColumnIdent.name).Nodup := by decide
  keys_ne_empty : keys != [] := by decide
  keys_mem_columns : ∀ k ∈ keys, k.name ∈ columns.map Column.name := by decide

instance : BEq Schema where
  beq s t := s.name == t.name && s.columns == t.columns && s.keys == t.keys

structure Key (s : SchemaIdent) where
structure Many (s : SchemaIdent) where

abbrev EDBType.asType : EDBType → Type
  | .elementary t => t.asType
  | .key s => Key s
  | .many s => Many s

def Schema.HasCol (s : Schema) (c : Column) : Prop := c ∈ s.columns

abbrev Values' : List Column → Type
  | [] => Unit
  | [c] => c.underlying.asType
  | c :: cs => c.underlying.asType × Values' cs

abbrev Values (s : Schema) : Type := Values' s.columns

/-- Auxiliary schema realizing a many-to-many relation .-/
structure AuxSchema where
  /-- The schema that is referred to by the remote schema. -/
  origin : Schema
  /-- The schema that has a many-to-many field with value in origin. -/
  remote : Schema
  colName : String
  /-- Evidence that remote has a many-to-many relation with origin. -/
  h : remote.HasCol (.mk colName <| .many <| .mk origin.name)

def Schema.keyColumns (s : Schema) : List Column :=
  s.columns.filter (fun c ↦ .mk c.name ∈ s.keys)

def AuxSchema.columns (a : AuxSchema) : List Column :=
  let rem : List Column := a.remote.keyColumns.map
    (fun c ↦ .mk s!"{a.remote.name}_{c.name}" c.underlying)
  let orig : List Column := a.origin.keyColumns.map
    (fun c ↦ .mk s!"{a.origin.name}_{c.name}" c.underlying)
  .mk "id" (.elementary .nat) :: rem ++ orig

def AuxSchema.toSchema (a : AuxSchema) : Schema where
  name := s!"aux_{a.origin.name}_{a.remote.name}"
  columns := a.columns
  keys := [.mk "id"]
  nodup_columns := sorry
  keys_mem_columns := by simp [AuxSchema.columns]

instance : BEq AuxSchema where
  beq x y := x.origin == y.origin && x.remote == y.remote && x.colName == y.colName

instance : ToString AuxSchema where
  toString as := s!"aux {as.origin.name}<-{as.remote.name}.{as.colName}"

def Column.toString (c : Column) : String := s!"column {c.name}"

def EDBType.toString (t : EDBType) : String := match t with
  | .elementary x => s!"elementary {ToString.toString x}"
  | .key s => s!"key {s.name}"
  | .many s => s!"many {s.name}"

instance : ToString EDBType where
  toString := EDBType.toString

structure Database where
  /-- A list of schemas. -/
  schemas : List Schema
  /-- A list of auxiliary schemas, needed for many-to-many relations -/
  auxschemas : List AuxSchema
  /-- No duplicate schema names. -/
  nodups : (schemas.map Schema.name).Nodup := by decide
  /- TODO: add validity condition on `auxschemas`: there should be exactly one
  auxschema for every many-to-many relation -/

def Database.HasSchema (d : Database) (s : Schema) : Prop := s ∈ d.schemas

section Example

def foo : Schema where
  name := "foo"
  columns := [.mk "id" (.elementary .int)]
  keys := [.mk "id"]

def baz : Schema where
  name := "baz"
  columns := 
    [ .mk "id" (.elementary .int)
    , .mk "one_foo" (.key <| .mk "foo")
    , .mk "some_foos" (.many <| .mk "foo")
    , .mk "other_foos" (.many <| .mk "foo")
    ]
  keys := [.mk "id"]

def bazDatabase : Database where
  schemas := [foo, baz]
  auxschemas :=
    [ .mk foo baz "some_foos" (by repeat constructor)
    , .mk foo baz "other_foos" (by repeat constructor)]

example : Values baz := (3, ⟨⟩, ⟨⟩, ⟨⟩)

end Example

-- (postgre)SQL specific
namespace PSQL

inductive Field where
  | varchar (n : Nat)
  | bool
  | nat
  | int

def Field.ofDBType : DBType → Field
  | .nat => .nat
  | .int => .int
  | .varchar n => .varchar n
  | .bool => .bool

structure Column where
  name : String
  field : Field

structure ForeignKey where
  originColumn : String
  remoteTable : String
  remoteColumn : String
  -- on delete etc.

structure Table where
  name : String
  fields : List Column
  keys : List String
  foreignKeys : List ForeignKey
  -- validity conditions, such as no duplicate names etc.

def mkTables (s : Schema) : Table where
  name := s.name
  fields := s.columns.filterMap <| fun c ↦
    match c.underlying with
    | .elementary t => Column.mk s.name (.ofDBType t)
    | _ => none
  keys := s.keys.map ColumnIdent.name
  foreignKeys := s.columns.filterMap <| fun c ↦
    match c.underlying with
    | .key ident => ForeignKey.mk sorry ident.name sorry
    | _ => none

end PSQL
