universe u v w

structure CharField where
  size : Nat
  verboseName : String

structure NatField where
  verboseName : String

class HasInterpretation (I : Sort v) (F : Sort u) where

class HasField (F : Sort u) (I : Sort v) (R : Sort w)
      [HasInterpretation I R] where
    /-- Interpret the field signature in the interpretation. -/
    interpretField : F → R

structure Column where
  ident : String
  type : Sort u
  val : type

def Column.mk' (ident : String) {type : Sort u} (val : type) : Column where
  ident := ident
  type := type
  val := val

structure Model where
  columns : List Column

class Model.HasTable (m : Model) (I : Sort v) (R : Sort u) [HasInterpretation I R] where
  hasFields : ∀ c ∈ m.columns, HasField c.type I R

/-- A many to many field represents an array of entries of a given model. -/
structure ManyToManyField where
  verboseName : String
  remote : Model
  -- add on delete behaviour etc.

-- postgreSQL specific
structure PSQL : Type where

namespace PSQL

inductive Field where
  | varchar (n : Nat)
  | nat
  | key (name : String)

instance : HasInterpretation PSQL Field where

instance : HasField CharField PSQL Field where
  interpretField x := .varchar x.size

instance : HasField NatField PSQL Field where
  interpretField _ := .nat

structure NamedField where
  name : String
  field : Field

structure Table where
  name : String
  fields : List NamedField
  -- validity conditions, such as no duplicate names etc.

def Table.ofModel (m : Model) [m.HasTable PSQL Field] : Table where
  name := sorry
  fields := m.columns.pmap (P := (· ∈ m.columns))
    (fun c (hc : c ∈ m.columns) ↦
      letI : HasField c.type PSQL Field := Model.HasTable.hasFields c hc
      ⟨c.ident, HasField.interpretField PSQL c.val⟩) (fun _ h ↦ h)

end PSQL
