/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Model.Meta.DatabaseTag

open Lean Elab Command

-- TODO: add `HasModel` instances for tables.
def elabDatabase (decl : Name) (tables : List (Name × Option String)) :
    CommandElabM Unit := do
  let indexName : Name := decl.capitalize ++ `Index
  elabEnum indexName <| tables.map fun (name, dbName?) =>
    (name, dbName?.getD name.toString)
  let tableMap : Expr ←
    liftTermElabM <|
      fromEnum indexName (tables.toArray.map fun t => .const t.1 []) (.const ``Table [])
  let database : Expr ← liftTermElabM <|
    Meta.mkAppM ``Database.mk #[.const indexName [], tableMap]
  let databaseDecl : Declaration :=
    .defnDecl
      { name := decl
        levelParams := []
        type := .const ``Database []
        value := database
        hints := default
        safety := .safe }
  liftCoreM <| addAndCompile databaseDecl

/-
TODOs:
- add safeguard checks if declaration already exists
-/
elab "initialize_database" decl:ident : command => do
  let auxDbDecl ← mkAuxDeclName
  elabDatabase auxDbDecl []
  addDatabaseTag decl.getId
    { databaseDecl := auxDbDecl
      tables := #[] }

initialize_database mydb

def addTableToDatabase (tableInfo : TableInfo) (database : Name) :
    CommandElabM Unit := do
  let some tag ← getDatabaseTag? database |
    throwError s!"Database `{database}` does not exist."
  let auxDbDecl ← mkAuxDeclName
  let newTables := tag.tables.push tableInfo
  elabDatabase auxDbDecl (newTables.toList.map fun info => (info.tableDecl, info.tableName))
  addDatabaseTag database
    { databaseDecl := auxDbDecl
      tables := newTables }

def updateHasModels (database : Name) : CommandElabM Unit := do
  let some dbTag ← getDatabaseTag? database
    | throwError "Database {database} does not exist."
  for table in dbTag.tables do
    if let some typeDecl := table.typeDecl? then
    let auxModelDecl ← mkAuxDeclName
    let modelStx ←
      `(def $(mkIdent auxModelDecl) :
            Model $(mkIdent dbTag.databaseDecl) $(mkIdent typeDecl) where
          index := $(mkIdent (dbTag.databaseDecl.capitalize ++ `Index ++ table.tableDecl))
          hasTable := inferInstanceAs <| HasTable _ $(mkIdent table.tableDecl))
    elabCommand modelStx
    let instStx ←
      `(instance : HasModel $(mkIdent typeDecl) where
          database := $(mkIdent dbTag.databaseDecl)
          model := $(mkIdent auxModelDecl))
    elabCommand instStx

def addHasModel (tableTypeDecl database : Name) : CommandElabM Unit := do
  let tableDecl : Name := s!"{tableTypeDecl}Table".toName
  let env ← getEnv
  let some _ := env.find? tableDecl
    | throwError "Could not find table for {tableTypeDecl}."
  let some dbTag ← getDatabaseTag? database
    | throwError "Database {database} does not exist."
  let modelDecl : Name := tableTypeDecl ++ `model
  let modelStx ←
    `(def $(mkIdent modelDecl) :
          Model $(mkIdent dbTag.databaseDecl) $(mkIdent tableTypeDecl) where
        index := $(mkIdent (dbTag.databaseDecl.capitalize ++ `Index ++ tableDecl))
        hasTable := inferInstanceAs <| HasTable _ $(mkIdent tableDecl))
  elabCommand modelStx
  let instStx ←
    `(instance : HasModel $(mkIdent tableTypeDecl) where
        database := $(mkIdent dbTag.databaseDecl)
        model := $(mkIdent modelDecl))
  elabCommand instStx

elab "add_table" tableTypeDecl:ident " to " database:ident : command => do
  let tableDecl : Name := s!"{tableTypeDecl.getId}Table".toName
  let info : TableInfo :=
    { tableDecl := tableDecl
      typeDecl? := tableTypeDecl.getId
      tableName := none }
  addTableToDatabase info database.getId
  -- addHasModel tableTypeDecl.getId database.getId
  updateHasModels database.getId

syntax (name := databaseTerm) "%database" ident : term

open Term

@[term_elab databaseTerm]
def elabDatabaseTerm : Term.TermElab := adaptExpander fun stx => do
  match stx with
  | `(%database $database:ident) =>
    let some tag ← getDatabaseTag? database.getId |
      throwError s!"Database `{database}` does not exist."
    `($(mkIdent tag.databaseDecl))
  | _ => throwUnsupportedSyntax
