/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Migration.Basic

structure Interpretation (query : Type) where
  fromQuery {d : Database} (names : Std.HashSet d.Name) (q : Query d names) : query

/-- An interpretation monad on the database `d` provides lookup and modification operations. -/
class DBMonad (d : Database) (m : Type → Type) where
  /-- Lookup the given query on the database. -/
  lookup {names : Std.HashSet d.Name} (q : Query d names) :
    m (Array (Std.DHashMap d.Name (fun d ↦ d.dbtype.Value)))
  /-- Insert the given data into the database. Return true if successful, false otherwise. -/
  insert {name : d.Index} (data : d.Insert name) : m Unit
  /-- Delete rows matching the expression. Return number of deleted rows. -/
  delete (e : DBExpr d .bool) : m Nat

class DBMonadWithMigrations (m : Type → Type) where
  [dbMonad (d : Database) : DBMonad d m]
  /-- Initialize with given database description. -/
  init (d : Database) : m Unit
  -- this does not work because `Database : Type 1`
  -- currentDatabase : m Database
  /-- Execute the given migration. -/
  migrate {source target : Database} (migration : source.Migration target) : m Unit
