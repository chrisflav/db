/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Utils.Enum
import Db.Model.Meta.GenerateTable
import Lean

open Lean Elab Command

structure TableInfo where
  tableDecl : Name
  typeDecl? : Option Name
  tableName : Option String
  deriving DecidableEq, Hashable

structure DatabaseTag where
  databaseDecl : Name
  tables : Array TableInfo
  -- TODO: support setting a different table-in-db name as string
  deriving DecidableEq, Hashable

initialize databaseExt : SimplePersistentEnvExtension (Name × DatabaseTag) (Std.HashMap Name DatabaseTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashMap.insertMany {}
    addEntryFn := fun m (k, x) => m.insert k x
  }

def addDatabaseTag {m : Type → Type} [MonadEnv m] (name : Name) (tag : DatabaseTag) : m Unit :=
  modifyEnv (databaseExt.addEntry · (name, tag))

def getDatabaseTags {m : Type → Type} [MonadEnv m] [Monad m] : m (Std.HashMap Name DatabaseTag) := do
  return databaseExt.getState (← getEnv)

def getDatabaseTag? {m : Type → Type} [MonadEnv m] [Monad m] (name : Name) :
    m (Option DatabaseTag) := do
  return (← getDatabaseTags)[name]?
