import Lean

/-
Fin cases tactic, implementation inspired by mathlib's `fin_cases` tactic.
-/

open Lean Elab

private def guardConcreteFin (expr : Expr) : MetaM Expr :=
  match expr.getAppFnArgs with
  | (``Fin, #[n]) => return n
  | _ => throwError "Variable not of type `Fin ?n` for concrete `?n`."

private def isMembership (expr : Expr) : Bool :=
  match expr.getAppFnArgs with
  | (``List.Mem, _) => true
  | (``Membership.mem, _) => true
  | _ => false

partial def finCases (goal : MVarId) (var : FVarId) : MetaM (List MVarId) := goal.withContext do
  let type ← var.getType >>= instantiateMVars
  let _ ← guardConcreteFin type
  let memListExpr ← Meta.mkAppM ``List.mem_finRange #[.fvar var]
  let type ← Meta.inferType memListExpr
  let (_, goal) ← (← goal.assert `this type memListExpr).intro1P
  goal.casesRec fun decl => return isMembership decl.type

elab "fincases" var:ident : tactic => do
  let fvar ← Tactic.getFVarId var
  Tactic.liftMetaTactic fun goal => finCases goal fvar

section Tests

def foobaz : Fin 3 → String
  | 0 => "ho"
  | 1 => "ho"
  | 2 => "ho"

example (i : Fin 3) : foobaz i = "ho" := by
  fincases i <;> rfl

end Tests
