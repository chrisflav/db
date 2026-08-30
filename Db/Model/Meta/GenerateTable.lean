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
import Db.Migration.Basic
import Db.Model.HasTable
import Db.Utils.FinCases

universe u

open Lean Elab Command

syntax (name := generateTableStx) "generate_table " ident : command

def mkEnumDeclaration (name : Name) (names : List Name) : Declaration :=
  Lean.mkInductiveDeclEs [] 0 [
    { name := name
      type := .sort 1
      ctors := names.map fun arg ↦ { name := name ++ arg, type := .const name [] } }
  ] false

def fromEnumWithoutMotive (name : Name) (expr : Array Expr) : MetaM Expr := do
  Meta.withLocalDecl `x BinderInfo.default (.const name []) fun x => do
    let body ← Meta.mkAppOptM (name ++ `casesOn) (#[none, some x] ++ (expr.map Option.some))
    Meta.mkLambdaFVars #[x] body

def fromDepEnum (name : Name) (expr : Array (Expr × Expr)) : MetaM Expr := do
  let motive : Expr ← fromEnum name (expr.map Prod.snd) (.sort 1)
  Meta.withLocalDecl `x BinderInfo.default (.const name []) fun x => do
    let body ← Meta.mkAppOptM (name ++ `casesOn)
      (#[some motive, some x] ++ (expr.map (Option.some ∘ Prod.fst)))
    Meta.mkLambdaFVars #[x] body

@[reducible] def FromString.ofToString (α : Type) [ToString α] [Enum α] : FromString α where
  fromString s := Id.run do
    let mut res : Option α := none
    for x in Enum.all α do
      if s == toString x then
        res := some x
    return res

def List.toExpr (type : Expr) : List Expr → MetaM Expr
  | [] => Meta.mkAppOptM ``List.nil #[some type]
  | e :: es => do Meta.mkAppM ``List.cons #[e, ← es.toExpr type]

/--
Produces roughly (where the list is `[(lhs1, rhs1), ...]`:
```
match var with
| lhs1 => rhs1
| lhs2 => rhs2
| ...
| _ => default
```
-/
def mkMatch (var : Expr) (default : Expr) : List (Expr × Expr) → MetaM Expr
  | [] => pure default
  | (comp, val) :: xs => do
    Meta.mkAppM
      ``cond #[← Meta.mkAppM ``BEq.beq #[var, comp], val, ← mkMatch var default xs]

open Qq

def mkFinMatch (l : List Expr) (var : Q(Fin $(l).length)) : Expr :=
  q($l[$var])

def elabEnum (name : Name) (names : List (Name × String)) : CommandElabM Unit := do
  let decl : Declaration :=
    mkEnumDeclaration name (names.map Prod.fst)
  liftCoreM <| addAndCompile decl
  liftTermElabM <| do
    mkCasesOn name
    mkCtorIdx name
  applyDerivingHandlers ``DecidableEq #[name]
  applyDerivingHandlers ``Hashable #[name]
  applyDerivingHandlers ``Enum #[name]
  let toString : Expr ← liftTermElabM <| do
    let val : Expr ←
      fromEnum name (names.toArray.map fun x ↦ .lit <| .strVal x.2) (.const ``String [])
    Meta.mkAppM ``ToString.mk #[val]
  elabInstance toString
  let fromString : Expr ← liftTermElabM <| do
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
      none, none, none, none, none]
    match (← Meta.inferType app).getForallArgs with
    | [(_name, type)] =>
      let e ← Meta.mkFreshExprMVar type
      _ ← Elab.runTactic e.mvarId! (← `(tactic| intro x; induction x <;> rfl))
      Meta.mkAppM' app #[e]
    | _ => throwError "Failed when constructing indexing instance."
  elabInstance indexing

/--
An integer primary key the database generates. A model field of this type becomes a single-column
auto-incrementing primary key, which an insert leaves out for the database to assign.

It is a `def` rather than a `structure` so that its values *are* the values of the column, which is
what the generated `HasTable` encoding needs, while still being a distinct head symbol for instance
resolution and for the field scan that finds the key.
-/
def AutoKey : Type := Int

instance : Repr AutoKey := inferInstanceAs (Repr Int)
instance : ToString AutoKey := inferInstanceAs (ToString Int)
instance : Inhabited AutoKey := inferInstanceAs (Inhabited Int)
instance : DecidableEq AutoKey := inferInstanceAs (DecidableEq Int)
instance : BEq AutoKey := inferInstanceAs (BEq Int)
instance (n : Nat) : OfNat AutoKey n := inferInstanceAs (OfNat Int n)
instance : FromString AutoKey := inferInstanceAs (FromString Int)

class HasDBType (α : Type) where
  type : DBType
  encoding : α ≃ type.Value

class HasColumn (α : Type) where
  column : Column
  encoding : α ≃ column.Value

instance : HasDBType Bool where
  type := .bool
  encoding := Equiv.refl _

instance (n : Nat) : HasDBType (VarChar n) where
  type := .varchar n
  encoding := Equiv.refl _

instance : HasDBType Int where
  type := .int
  encoding := Equiv.refl _

instance : HasDBType String where
  type := .text
  encoding := Equiv.refl _

instance : HasColumn AutoKey where
  column := { type := .int, nullable := false, autoIncrement := true }
  encoding := Equiv.refl _

instance (α : Type) [HasDBType α] : HasColumn α where
  column.type := HasDBType.type α
  column.nullable := false
  encoding := HasDBType.encoding

instance (α : Type) [HasDBType α] : HasColumn (Option α) where
  column.type := HasDBType.type α
  column.nullable := true
  encoding := HasDBType.encoding.optionCongr

/-- Add `HasTable` instance for `decl` with table `tableName`. -/
def generateHasTable (decl indexName tableName : Name) : CommandElabM Unit := do
  let fields ← getStructureArgs decl
  let equiv : Expr ← liftTermElabM <| do
    let entryType : Expr ← Meta.mkAppM ``Table.Entry #[.const tableName []]
    let toFun : Expr ← Meta.withLocalDecl `x BinderInfo.default (.const decl []) fun x => do
      let motive : Expr ←
        Meta.withLocalDecl `x BinderInfo.default (.const indexName []) fun x => do
          let body ← Meta.mkAppM ``Column.Value #[
            ← Meta.mkAppM ``Table.columns #[.const tableName [], x]
          ]
          Meta.mkLambdaFVars #[x] body
      let body : Expr ← do
        Meta.mkAppOptM ``Table.Entry.mk #[
          Expr.const tableName [],
          ← fromEnumWithMotive indexName
            (← (fields.toArray.mapM fun f => Meta.mkAppM (decl ++ f.1) #[x]))
            motive
        ]
      Meta.mkLambdaFVars #[x] body
    let invFun : Expr ← Meta.withLocalDecl `x BinderInfo.default entryType fun x => do
      -- The values function of the entry
      let valFun : Expr ← Meta.mkAppM ``Table.Entry.value #[x]
      let body : Expr ← do
        -- Construct term of structure
        Meta.mkAppM (decl ++ `mk)
          -- for every field of the structure
          (← fields.toArray.mapM
            fun f => do pure <|
            -- evaluate the values function
            ← Meta.mkAppM' valFun #[← Meta.mkAppM (indexName ++ f.1) #[]])
      Meta.mkLambdaFVars #[x] body
    let appEquiv ← Meta.mkAppOptM ``Equiv.mk #[Expr.const decl [], entryType, toFun, invFun]
    match (← Meta.inferType appEquiv).getForallArgs with
    | [(_name₁, type₁), (_name₂, type₂)] =>
      let e₁ ← Meta.mkFreshExprMVar type₁
      _ ← Elab.runTactic e₁.mvarId!
        (← `(tactic| intro x; induction x <;> rfl))
      let e₂ ← Meta.mkFreshExprMVar type₂
      _ ← Elab.runTactic e₂.mvarId!
        (← `(tactic| intro x; induction x <;> ext y <;> induction y <;> rfl))
      Meta.mkAppM' appEquiv #[e₁, e₂]
    | _ => throwError "Failed when constructing `HasTable`."
  let inst : Expr ← liftTermElabM <|
    Meta.mkAppOptM ``HasTable.mk #[none, Expr.const tableName [], equiv]
  elabInstance inst

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
      Meta.mkAppOptM ``HasColumn.column #[some type, none]
  let colMap : Expr ←
    liftTermElabM <| fromEnum indexName cols (.const ``Column [])
  -- The field of type `AutoKey`, if there is one, is the primary key. More than one is not a
  -- schema either backend can create: a generated column has to be the whole primary key.
  let keyFields := names.filter fun (_, type) => type.isConstOf ``AutoKey
  if keyFields.length > 1 then
    throwError m!"`{decl}` has more than one `AutoKey` field: \
      {String.intercalate ", " (keyFields.map (·.1.toString))}. A generated key has to be \
      the whole primary key, so at most one is allowed."
  -- Construct `Table` and add to environment
  let table : Expr ← liftTermElabM <| do
    let idx : Expr := .const indexName []
    let primaryKey ← List.asExpr idx (keyFields.map fun (n, _) => .const (indexName ++ n) [])
    let unique ← Meta.mkAppOptM ``List.nil #[some (← Meta.mkAppM ``List #[idx])]
    let foreignKeys ← Meta.mkAppOptM ``List.nil #[some (← Meta.mkAppM ``ForeignKey #[idx])]
    Meta.mkAppOptM ``Table.mk
      #[some idx, none, some colMap, some primaryKey, some unique, some foreignKeys]
  let tableDecl : Declaration :=
    .defnDecl
      { name := tableName
        levelParams := []
        type := .const ``Table []
        value := table
        hints := default
        safety := .safe }
  liftCoreM <| addAndCompile tableDecl
  generateHasTable decl indexName tableName

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
example : Enum.encoding.invFun 0 = BazIndex.val := rfl

end Example
