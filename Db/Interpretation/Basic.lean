/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Migration.Basic
import Db.Migration.Recipe

structure Interpretation (query : Type) where
  fromQuery {d : Database} (names : Std.HashSet d.Name) (q : Query d names) : query

-- TODO: Should also support logging operations for a custom error type
/-- An interpretation monad on the database `d` provides lookup and modification operations. -/
class DBMonad (d : Database) (m : Type → Type) where
  /-- Lookup the given query on the database. -/
  lookup {names : Std.HashSet d.Name} (q : Query d names) :
    m (Array (Std.DHashMap d.Name (fun d ↦ d.column.Value)))
  /-- Insert the given data into the database. Return true if successful, false otherwise. -/
  insert {name : d.Index} (data : d.Insert name) : m Unit
  /-- Delete rows matching the expression. Return number of deleted rows. -/
  delete (e : DBExpr d .bool) : m Nat

class DBMonadWithMigrations (m : Type → Type) where
  [dbMonad (d : Database) : DBMonad d m]
  /- Initialize with given database description. -/
  -- init (d : Database) : m Unit
  /-- The current database configuration. -/
  currentDatabase : m DatabaseRecipe
  /- Execute the given operation. -/
  execute (op : DatabaseOperation) : m Unit

namespace DBMonadWithMigrations

attribute [instance] DBMonadWithMigrations.dbMonad

variable {m : Type → Type} [DBMonadWithMigrations m] [Monad m]

def executeMany (operations : Array DatabaseOperation) : m Unit := do
  operations.forM execute

def init (database : DatabaseRecipe) : m Unit := do
  executeMany <| DatabaseRecipe.operations ∅ database

/-- Automatically update the current database schema to match `target`. -/
def autoUpdate (target : DatabaseRecipe) : m Unit := do
  let source ← currentDatabase
  executeMany <| source.operations target

end DBMonadWithMigrations
