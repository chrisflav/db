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

class HasView (α : Type) where
  database (α) : Database
  view (α) : View database
  encoding : α ≃ view.Entry

-- TODO: add meta code / DSL (?) to construct querysets for models
/-- A queryset for a model `m` is a query on the corresponding database table. -/
protected def Model.Query {d : Database} {α : Type} (model : Model d α) : Type 1 :=
  _root_.Query d (Table.view model.index)

variable {m : Type → Type} [DBMonad d m] [Monad m] [MonadExcept String m]

/-- Fetch the given queryset from the database. -/
def Model.Query.fetch (q : model.Query) : m (Array α) := do
  let res ← DBMonad.lookup q
  return res.map fun entry =>
    HasTable.encoding.invFun ((Table.entryViewEquiv model.index).toFun entry)

def Model.insert (model : Model d α) (a : α) : m Unit := do
  let data : d.Insert model.index :=
    { entry := (Table.entryViewEquiv _).invFun <| HasTable.encoding.toFun a }
  DBMonad.insert data

/-- A queryset on a type with canonical model is a query on the model. -/
structure QuerySet (α : Type) [HasView α] where
  query : Query (HasView.database α) (HasView.view α)

instance [HasModel α] : HasView α where
  database := HasModel.database α
  view := Table.view (HasModel.model _).index
  encoding := .trans HasTable.encoding (Table.entryViewEquiv _).symm

namespace QuerySet

variable {α : Type} [HasModel α]

def all : QuerySet α where
  query := .all _

end QuerySet

namespace QuerySet

variable {α : Type} [HasView α]

/-- Sort the rows of a query set by the given keys, in order. -/
def orderBy (q : QuerySet α) (keys : List (SortKey (HasView.view α))) : QuerySet α where
  query := .orderBy keys q.query

/-- Keep at most `n` rows. Applied after `orderBy`, so that it selects the first `n` rows of the
sorted result. -/
def limit (q : QuerySet α) (n : Nat) : QuerySet α where
  query := .limit n q.query

/-- Skip the first `n` rows. -/
def offset (q : QuerySet α) (n : Nat) : QuerySet α where
  query := .offset n q.query

/-
book where book.author = author.name ∧
           author.retired = True
-/

end QuerySet

namespace HasModel

variable {α : Type} [HasModel α]
variable {m : Type → Type} [DBMonadWithMigrations m] [Monad m] [MonadExcept String m]

def fetch (q : QuerySet α) : m (Array α) := do
  let res ← DBMonad.lookup q.query
  return res.map HasView.encoding.invFun

def insert (x : α) : m Unit :=
  (HasModel.model α).insert x

/-- The number of rows the query set matches, counted by the database rather than by fetching the
rows and counting them here. -/
def count (q : QuerySet α) : m Int := do
  let rows ← DBMonad.lookup (d := HasView.database α) q.query.countAll
  return (rows[0]?.map View.singletonValue).getD 0

/-- Delete every row of `α`'s table matching the boolean condition `e`, returning the number of
rows deleted. Build `e` from the model's column indices, e.g. `.eq (.var .author _) (.str v"Lisa")`. -/
def delete (e : DBExpr (HasView.database α) (HasView.view α) .bool) : m Nat :=
  DBMonad.delete (d := HasView.database α) e

end HasModel
