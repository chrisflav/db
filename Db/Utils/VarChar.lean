/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Lean.Parser.Term
import Db.Utils.FromString

/-- A string of length bounded by `n`. -/
structure VarChar (n : Nat) where
  val : String
  length_le : val.length ≤ n := by decide
  deriving Repr

instance {n : Nat} (x : VarChar n) : CoeDep (VarChar n) x String where
  coe := x.val

instance (n : Nat) : ToString (VarChar n) where
  toString := VarChar.val

instance (n : Nat) : FromString (VarChar n) where
  fromString s := if h : s.length ≤ n then some ⟨s, h⟩ else none

/-- The parser of the `v"..."` literal, e.g. `v"Mike" : VarChar 4`.

`v` is deliberately *not* a reserved token: it is parsed as a non-reserved symbol, so that `v` stays
an ordinary identifier — a local, a binder, a field — in every module that imports this one. That
costs a hand-written parser rather than a plain `syntax` declaration, because a non-reserved symbol
is lexed as an identifier, and only `includeIdent := true` registers the parser under the identifier
token, which is what the `term` category looks up. The literal binds at `maxPrec` and demands that
the string follow with no whitespace, so `f v "s"` is still `f` applied to `v` and to a string. -/
@[term_parser] def VarChar.lit : Lean.Parser.Parser :=
  open Lean.Parser in
  leading_parser:maxPrec
    nonReservedSymbol "v" (includeIdent := true) >>
      checkNoWsBefore "no space before the string of a `v\"...\"` literal" >> strLit

/-- Expand `v"..."` into `VarChar.mk "..."`, whose length bound comes from the expected type and
whose `length_le` proof is the `by decide` default of the structure. -/
@[macro VarChar.lit] def VarChar.expandLit : Lean.Macro := fun stx => do
  let s := stx[1]
  unless s.isOfKind Lean.strLitKind do Lean.Macro.throwUnsupported
  `(VarChar.mk $(⟨s⟩))
