/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Lean.Elab.Command

open Lean Elab

structure ModelTag where
  declName : Name
  -- TODO: add meta information
  deriving DecidableEq, Hashable

initialize tagExt : SimplePersistentEnvExtension ModelTag (Std.HashSet ModelTag) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

def addModelTag {m : Type → Type} [MonadEnv m] (tag : ModelTag) : m Unit :=
  modifyEnv (tagExt.addEntry · tag)

syntax (name := modelTag) "model" : attr

initialize Lean.registerBuiltinAttribute {
  name := `modelTag
  descr := "Tag a structure with a model tag"
  add decl stx _ := do
    match stx with
    | `(attr| model) => addModelTag { declName := decl }
    | _ => throwUnsupportedSyntax
}
