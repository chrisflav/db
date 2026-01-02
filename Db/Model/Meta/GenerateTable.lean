/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Lean.Elab.Tactic.Meta
import Lean.Elab.Command
import Lean.Elab.Deriving.Basic
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Constructions.CasesOn
import Db.Query.Basic
import Db.Utils.Equiv

open Lean Elab Command

def Lean.Expr.getForallArgs : Expr → List (Name × Expr)
  | .forallE n t b _ => (n, t) :: getForallArgs b
  | _ => []

syntax (name := generateTableStx) "generate_table " ident : command

def getStructureArgs {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (decl : Name) :
    m (List (Name × Expr)) := do
  let .inductInfo info := ← getConstInfo decl | throwError "Not a structure."
  unless info.ctors.length == 1 do throwError "Not a structure."
  let ctor := info.ctors[0]!
  let ctorInfo ← getConstInfo ctor
  return ctorInfo.type.getForallArgs

def mkEnumDeclaration (name : Name) (names : List Name) : Declaration :=
  Lean.mkInductiveDeclEs [] 0 [
    { name := name
      type := .sort 1
      ctors := names.map fun arg ↦ { name := name ++ arg, type := .const name [] } }
  ] false

def fromEnum (name : Name) (expr : Array Expr) (type : Expr) : MetaM Expr := do
  let motive : Expr ← Meta.withLocalDecl `x BinderInfo.default (.const name []) fun x => do
    Meta.mkLambdaFVars #[x] type
  Meta.withLocalDecl `x BinderInfo.default (.const name []) fun x => do
    let body ← Meta.mkAppOptM (name ++ `casesOn) (#[some motive, some x] ++ (expr.map Option.some))
    Meta.mkLambdaFVars #[x] body

def FromString.ofToString (α : Type) [ToString α] [Enum α] : FromString α where
  fromString s := Id.run do
    let mut res : Option α := none
    for x in Enum.all α do
      if s == toString x then
        res := some x
    return res

def List.toExpr (type : Expr) : List Expr → MetaM Expr
  | [] => Meta.mkAppOptM ``List.nil #[some type]
  | e :: es => do Meta.mkAppM ``List.cons #[e, ← es.toExpr type]

def elabInstance (expr : Expr) : CommandElabM Unit := do
  let instName : Name ← Lean.mkAuxDeclName
  let instDecl : Declaration := .defnDecl
    { name := instName
      levelParams := []
      type := ← liftTermElabM <| Meta.inferType expr
      value := expr
      hints := default
      safety := .safe }
  liftCoreM <| addAndCompile instDecl
  liftTermElabM <| Meta.addInstance instName default 1000

def mkMatch (var : Expr) (default : Expr) : List (Expr × Expr) → MetaM Expr
  | [] => pure default
  | (comp, val) :: xs => do
    Meta.mkAppM
      ``cond #[← Meta.mkAppM ``BEq.beq #[var, comp], val, ← mkMatch var default xs]

def elabEnum (name : Name) (names : List (Name × String)) : CommandElabM Unit := do
  let decl : Declaration :=
    mkEnumDeclaration name (names.map Prod.fst)
  liftCoreM <| addAndCompile decl
  liftTermElabM <| do
    mkCasesOn name
    mkCtorIdx name
  applyDerivingHandlers ``DecidableEq #[name]
  applyDerivingHandlers ``Hashable #[name]
  let toString : Expr ← liftTermElabM <| do
    let val : Expr ←
      fromEnum name (names.toArray.map fun x ↦ .lit <| .strVal x.2) (.const ``String [])
    Meta.mkAppM ``ToString.mk #[val]
  elabInstance toString
  let enum : Expr ← liftTermElabM <| do
    let arr : Expr ← Meta.mkAppM ``Array.mk
      #[← (names.map fun x ↦ .const (name ++ x.1) []).toExpr (.const name [])]
    let val : Expr ←
      Meta.mkAppOptM ``Std.HashSet.ofArray
        #[Expr.const name [], none, none, arr]
    Meta.mkAppM ``Enum.mk #[val]
  elabInstance enum
  let fromString : Expr ← liftTermElabM <| do
    -- Meta.mkAppM ``FromString.ofToString #[.const name []]
    let val : Expr ←
      Meta.withLocalDecl `x BinderInfo.default (.const ``String []) fun x => do
        let body : Expr ← do
          mkMatch
            x
            (← Meta.mkAppOptM ``Option.none #[Expr.const name []])
            (← names.mapM fun y => do pure (.lit <| .strVal y.2,
              ← Meta.mkAppM ``Option.some #[.const (name ++ y.1) []]))
        Meta.mkLambdaFVars #[x] body
    Meta.mkAppM ``FromString.mk #[val]
  elabInstance fromString
  let indexing : Expr ← liftTermElabM <| do
    let app ← Meta.mkAppOptM ``Indexing.mk #[Expr.const name [],
      none, none, none]
    match (← Meta.inferType app).getForallArgs with
    | [(_name, type)] =>
      let e ← Meta.mkFreshExprMVar type
      _ ← Elab.runTactic e.mvarId! (← `(tactic| intro x; induction x <;> rfl))
      Meta.mkAppM' app #[e]
    | vars =>
      logInfo s!"{vars}"
      return app
  elabInstance indexing

class HasDBType (α : Type) where
  dbType : DBType
  encoding : α ≃ dbType.Value

instance : HasDBType Bool where
  dbType := .bool
  encoding := Equiv.refl _

instance (n : Nat) : HasDBType (VarChar n) where
  dbType := .varchar n
  encoding := Equiv.refl _

instance : HasDBType Int where
  dbType := .int
  encoding := Equiv.refl _

/-- Generate a `Table` for structure named `decl`. -/
def generateTable (decl : Name) : CommandElabM Unit := do
  let names ← getStructureArgs decl
  let indexName : Name := (s!"{decl}Index").toName
  let tableName : Name := (s!"{decl}Table").toName
  -- Add indexing type
  elabEnum indexName (names.map fun x ↦ (x.1, x.1.toString))
  -- Construct `Index → Column`
  let cols : Array Expr ← liftTermElabM <|
    names.toArray.mapM fun (_, type) ↦ do
      let dbtype : Expr ← Meta.mkAppOptM ``HasDBType.dbType #[some type, none]
      Meta.mkAppM ``Column.mk
        #[dbtype, .const ``Bool.false []]
  let colMap : Expr ←
    liftTermElabM <| fromEnum indexName cols (.const ``Column [])
  -- Construct `Table` and add to environment
  let table : Expr ← liftTermElabM <|
    Meta.mkAppM ``Table.mk #[.const indexName [], colMap]
  let tableDecl : Declaration :=
    .defnDecl
      { name := tableName
        levelParams := []
        type := .const ``Table []
        value := table
        hints := default
        safety := .safe }
  liftCoreM <| addAndCompile tableDecl

@[command_elab generateTableStx]
def generateTableElab : CommandElab
  | `(command| generate_table $decl) => generateTable decl.getId
  | _ => throwUnsupportedSyntax

section Example

structure Baz where
  val : Bool
  name : VarChar 10
  val2 : Int

generate_table Baz

example : (BazTable.columns .val).type = .bool := rfl
example : (BazTable.columns .val2).type = .int := rfl

end Example
