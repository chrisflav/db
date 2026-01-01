import Db.Query.Basic
import Db.Utils.Equiv

structure Indexing.Map {α β : Type} [Indexing α] [Indexing β] (f : α → β) : Prop where
  toString_apply (a : α) : ToString.toString (f a) = ToString.toString a

structure Table.Migration (source target : Table) where
  map : source.Index → target.Index

/--
A migration from database stage `source` to database stage `target`
is a recipe how to turn data in `source` into data in `target`.
-/
structure Database.Migration (source target : Database) where
  map : source.Index → target.Index
  indexing : Indexing.Map map
  entry (i : source.Index) (e : (source.tables i).Entry) : (target.tables (map i)).Entry

inductive Column.MigrationStep (column : Column) where

inductive Table.MigrationStep (table : Table) where
  | addColumn (column : Column) (name : String)
  | modifyColumn (column : Column) (step : column.MigrationStep)
  | dropColumn (name : table.Index)
  | reindex (T : Type) [Indexing T] (e : table.Index ≃ T)

inductive Database.MigrationStep (database : Database) where
  | createTable (table : Table) (name : String)
  | modifyTable (table : Table) (step : table.MigrationStep)
  | dropTable (name : database.Index)
  | reindex (T : Type) [Indexing T] (e : database.Index ≃ T)

def Table.addColumn (table : Table) (name : String) (col : Column) : Table :=
  haveI : Disjoint table.Index (IUnit name) := sorry
  { Index := table.Index ⊕ IUnit name
    columns := Sum.elim table.columns fun _ ↦ col }

def Table.MigrationStep.result {table : Table} : table.MigrationStep → Table
  | reindex T e =>
    { Index := T
      columns := table.columns ∘ e.invFun }
  | addColumn col name => table.addColumn name col
  | _ => sorry
