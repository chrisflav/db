/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Migration.Basic
import Db.Migration.Recipe

structure Interpretation (query : Type) where
  fromQuery {d : Database} (view : View d) (q : Query d view) : query

-- TODO: Should also support logging operations for a custom error type
/-- An interpretation monad on the database `d` provides lookup and modification operations. -/
class DBMonad (d : Database) (m : Type → Type) where
  /-- Lookup the given query on the database. -/
  lookup {view : View d} (q : Query d view) : m (Array view.Entry)
  /-- Insert the given data into the database. -/
  insert {name : d.Index} (data : d.Insert name) : m Unit
  /-- Insert the given data and return the rows the database stored, which is how the value of a
  generated column is obtained without a second query. -/
  insertReturning {name : d.Index} (data : d.Insert name) : m (Array (Table.view name).Entry)
  /-- Apply the update. Return the number of rows changed. -/
  update {name : d.Index} (upd : d.Update name) : m Nat
  /-- Apply the update and return the rows as they now are. An update that sets no column at all
  is not run and returns no rows, whatever its condition matches. -/
  updateReturning {name : d.Index} (upd : d.Update name) : m (Array (Table.view name).Entry)
  /-- Delete the rows the condition matches. Return the number of rows deleted. -/
  delete {name : d.Index} (del : d.Delete name) : m Nat
  /-- Delete the rows the condition matches and return them as they last were. -/
  deleteReturning {name : d.Index} (del : d.Delete name) : m (Array (Table.view name).Entry)

/--
A monad in which several database operations can be grouped into one atomic unit: either all of
them take effect or none of them do.
-/
class DBMonadTransactional (m : Type → Type) where
  /-- Run `x` inside a transaction, committing it if `x` succeeds and rolling it back if it
  fails. -/
  withTransaction {α : Type} (x : m α) : m α

class DBMonadWithMigrations (m : Type → Type) where
  [dbMonad (d : Database) : DBMonad d m]
  /- Initialize with given database description. -/
  -- init (d : Database) : m Unit
  /-- The current database configuration. -/
  currentDatabase : m DatabaseRecipe
  /- Execute the given operation. -/
  execute (op : DatabaseOperation) : m Unit
  /-- Create or drop one index. Separate from `execute` because the operation language describes
  column changes only, and an index is not one: it is an object beside the table, said whole by a
  single `CREATE INDEX` or `DROP INDEX`. -/
  executeIndex (op : IndexOperation) : m Unit
  /-- Give up on a migration that cannot be carried out, reporting why. -/
  abort {α : Type} (message : String) : m α

namespace DBMonadWithMigrations

attribute [reducible, instance] DBMonadWithMigrations.dbMonad

variable {m : Type → Type} [DBMonadWithMigrations m] [Monad m]

def executeMany (operations : Array DatabaseOperation) : m Unit := do
  operations.forM execute

def init (database : DatabaseRecipe) : m Unit := do
  executeMany <| DatabaseRecipe.operations ∅ database

/-- Automatically update the current database schema to match `target`.

The operation language describes column changes only, so a table whose constraints differ from the
target aborts the migration instead of being brought into a state that only looks like the target
schema. -/
def autoUpdate (target : DatabaseRecipe) : m Unit := do
  let source ← currentDatabase
  letI mismatches := source.constraintMismatches target
  unless mismatches.isEmpty do
    abort <|
      s!"the constraints of the table(s) {", ".intercalate mismatches.toList} differ from those " ++
        "of the target schema. A constraint change on an existing table is not migrated; " ++
        "migrate these by hand, or drop and recreate the tables."
  executeMany <| source.operations target
  -- Indexes after the columns, and against the schema as it now is rather than as it was: an index
  -- on a column this migration just added cannot be created before the column exists, and SQLite
  -- rebuilds a table to change a column type, which takes that table's indexes with it and puts
  -- them back. Reading the schema again is what makes both of those come out right.
  let migrated ← currentDatabase
  for op in migrated.indexOperations target do
    executeIndex op

end DBMonadWithMigrations
