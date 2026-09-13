/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Lean.Elab.Command
import Db.Model.Meta.Database

open Lean Elab

structure ModelTag where
  declName : Name
  database : Name
  -- TODO: add meta information
  deriving DecidableEq, Hashable

initialize tagExt : SimplePersistentEnvExtension ModelTag (Std.HashSet ModelTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addModelTag {m : Type → Type} [MonadEnv m] (tag : ModelTag) : m Unit :=
  modifyEnv (tagExt.addEntry · tag)

structure ModelConfig where
  /-- The name of the table in the database; the name of the structure if this is absent. -/
  dbName : Option String := none
  /-- The fields that are the table's primary key, in the order they are the key in:
  `(primaryKey := ["id"])`, or `(primaryKey := ["session_id", "seq"])` for a composite one.

  Empty for a model that declares none, whose key is then its `AutoKey` field if it has one and
  nothing at all otherwise. A declared key and an `AutoKey` field together are refused: a generated
  key has to be the whole primary key. -/
  primaryKey : List String := []
  deriving Inhabited

declare_command_config_elab elabModelConfig ModelConfig

syntax (name := modelTag) "model" Parser.Tactic.optConfig ident : attr

def elabModelTag (cfg : ModelConfig) (decl database : Name) : AttrM Unit := do
  let some _ ← getDatabaseTag? database
    | throwError s!"Unknown database `{database}`."
  liftCommandElabM <| do
    generateTable decl cfg.primaryKey
    let tableInfo : TableInfo :=
      { tableDecl := s!"{decl}Table".toName
        typeDecl? := decl
        tableName := cfg.dbName }
    addTableToDatabase tableInfo database
    updateHasModels database
  addModelTag
    { declName := decl
      database := database }

initialize Lean.registerBuiltinAttribute {
  name := `modelTag
  descr := "Tag a structure with a model tag"
  add decl stx _ := do
    match stx with
    | `(attr| model $c:optConfig $database:ident) =>
      let cfg ← liftCommandElabM <| elabModelConfig c
      elabModelTag cfg decl database.getId
    | _ => throwUnsupportedSyntax
}
