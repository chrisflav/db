/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Query.Basic
import Db.Utils.Equiv
import Db.Interpretation.Basic

/-- A type is associated with a database table if there
is an equivalence with the entries of the table. -/
class HasTable (α : Type) (t : Table) where
  encoding : α ≃ t.Entry

variable (α : Type) (t : Table) [HasTable α t]

structure Model (d : Database) (α : Type) where
  index : d.Index
  [hasTable : HasTable α (d.tables index)]

attribute [instance] Model.hasTable

variable {d : Database} {α : Type} {model : Model d α}

abbrev Model.table (model : Model d α) : Table :=
  d.tables model.index

/-- Typeclass expressing that `α` has a chosen model in a database. -/
class HasModel (α : Type) where
  database (α) : Database
  model (α) : Model database α

-- TODO: add meta code / DSL (?) to construct querysets for models
/-- A queryset for a model `m` is a query on the corresponding database table. -/
protected def Model.Query {d : Database} {α : Type} (model : Model d α) : Type 1 :=
  _root_.Query d (Table.names model.index)

variable {m : Type → Type} [DBMonad d m] [Monad m] [MonadExcept String m]

/-- Fetch the given queryset from the database. -/
def Model.Query.fetch (q : model.Query) : m (Array α) := do
  let res ← DBMonad.lookup q
  res.filterMapM fun map => OptionT.run do
    let x : model.table.Entry ← .mk <$> Enum.distribM fun c =>
      let val := map.get? (.ident { tableName := model.index, columnName := c})
      match val with
      | some val => return val
      | none =>
        -- TODO: add logging here
        failure
    return HasTable.encoding.invFun x

def Model.insert (model : Model d α) (a : α) : m Unit := do
  let data : d.Insert model.index :=
    { entry := HasTable.encoding.toFun a }
  DBMonad.insert data

/-- A queryset on a type with canonical model is a query on the model. -/
structure QuerySet (α : Type) [HasModel α] where
  query : (HasModel.model α).Query

namespace QuerySet

variable {α : Type} [HasModel α]

def all : QuerySet α where
  query := .all _

end QuerySet

namespace HasModel

variable {α : Type} [HasModel α]
variable {m : Type → Type} [DBMonadWithMigrations m] [Monad m] [MonadExcept String m]

def fetch (q : QuerySet α) : m (Array α) :=
  q.query.fetch

def insert (x : α) : m Unit :=
  (HasModel.model α).insert x

end HasModel
