import Lean
import Db.Utils.Equiv
import Db.Utils.FinCases
import Std
import Qq

universe u' u

class Enum (α : Type u) where
  length (α) : Nat
  encoding : α ≃ (Fin length)

instance (n : Nat) : Enum (Fin n) where
  length := n
  encoding := .refl _

def Enum.all (α : Type u) [Enum α] : Array α :=
  .ofFn Enum.encoding.invFun

def Fin.distribM {m : Type u → Type u'} [Monad m] {n : Nat} {α : Fin n → Type u}
    (f : (i : Fin n) → m (α i)) : m ((i : Fin n) → α i) :=
  match n with
  | 0 => pure fun i => False.elim (by grind [i.2])
  | n + 1 => do
    let g : (i : Fin n) → α ⟨i.1, by grind⟩ ←
      distribM fun j => f ⟨j.1, by grind⟩
    let x ← f (.last n)
    return fun j =>
      if hj : j < n
        then
          g ⟨j, by grind⟩
        else
          cast (congrArg _ <| by grind) x

def Enum.distribM {α : Type u} [Enum α] {m : Type u → Type u'} [Monad m] {β : α → Type u}
    (f : (a : α) → m (β a)) :
    m ((a : α) → β a) := do
  let g ← Fin.distribM fun i => f <| Enum.encoding.invFun i
  return fun a => cast (congrArg _ <| by simp) <| g (Enum.encoding.toFun a)

open Qq Lean Elab Command

def fromEnumWithMotive (name : Name) (expr : Array Expr) (motive : Expr) : MetaM Expr := do
  Meta.withLocalDecl `x BinderInfo.default (.const name []) fun x => do
    let body ← Meta.mkAppOptM (name ++ `casesOn) (#[some motive, some x] ++ (expr.map Option.some))
    Meta.mkLambdaFVars #[x] body

def fromEnum (name : Name) (expr : Array Expr) (type : Expr) : MetaM Expr := do
  let motive : Expr ← Meta.withLocalDecl `x BinderInfo.default (.const name []) fun x => do
    Meta.mkLambdaFVars #[x] type
  fromEnumWithMotive name expr motive

def Lean.Expr.getForallArgs : Expr → List (Name × Expr)
  | .forallE n t b _ => (n, t) :: getForallArgs b
  | _ => []

def getStructureArgs {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] (decl : Name) :
    m (List (Name × Expr)) := do
  let .inductInfo info := ← getConstInfo decl | throwError "Not a structure."
  unless info.ctors.length == 1 do throwError "Not a structure."
  let ctor := info.ctors[0]!
  let ctorInfo ← getConstInfo ctor
  return ctorInfo.type.getForallArgs

def Fin.asExpr {n : Nat} (i : Fin n) : Expr :=
  q($i)

def List.asExpr (type : Expr) : List Expr → MetaM Expr
  | [] => Meta.mkAppOptM ``List.nil #[type]
  | x :: xs => do Meta.mkAppM ``List.cons #[x, ← xs.asExpr type]

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

def deriveEnum (declNames : Array Name) : CommandElabM Bool := do
  unless declNames.size = 1 do return false
  let decl := declNames[0]!
  let .inductInfo info := ← getConstInfo decl | throwError "Not a structure."
  let fields : List Name := info.ctors
  let fieldsWithIdx : List (Name × Fin fields.length) :=
    fields.zip (List.finRange fields.length)
  let enum : Expr ← liftTermElabM <| do
    let length : Expr := .lit <| .natVal fields.length
    let finType : Expr ← Meta.mkAppM ``Fin #[length]
    let equiv : Expr ← do
      let toFun : Expr ←
        fromEnum declNames[0]!
          (fieldsWithIdx.toArray.map fun f => f.2.asExpr)
          finType
      let invFun : Expr ← Meta.withLocalDecl `x BinderInfo.default finType fun x => do
        let listExpr : Expr ←
          List.asExpr (.const declNames[0]! []) (fields.map fun x => .const (x) [])
        let body ← Meta.mkAppM ``List.get #[listExpr, x]
        Meta.mkLambdaFVars #[x] body
      let appEquiv ← Meta.mkAppOptM ``Equiv.mk #[Expr.const declNames[0]! [], finType, toFun, invFun]
      match (← Meta.inferType appEquiv).getForallArgs with
      | [(_name₁, type₁), (_name₂, type₂)] =>
        let e₁ ← Meta.mkFreshExprMVar type₁
        _ ← Elab.runTactic e₁.mvarId!
          (← `(tactic| intro x; induction x <;> rfl))
        let e₂ ← Meta.mkFreshExprMVar type₂
        _ ← Elab.runTactic e₂.mvarId!
          (← `(tactic| intro i; fincases i <;> rfl))
        Meta.mkAppM' appEquiv #[e₁, e₂]
      | _ => throwError "Failed when constructing `Enum` instance."
    Meta.mkAppM ``Enum.mk #[length, equiv]
  elabInstance enum
  return true

initialize registerDerivingHandler ``Enum deriveEnum

section Test

elab "derive_enum" name:ident : command => do
  _ ← deriveEnum #[name.getId]

inductive Baboosh
  | a
  | b
  | c

derive_enum Baboosh

example : Enum.encoding.invFun 1 = Baboosh.b := rfl

end Test
