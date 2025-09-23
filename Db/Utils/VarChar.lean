/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-- A string of length bounded by `n`. -/
structure VarChar (n : Nat) where
  val : String
  length_le : val.length ≤ n := by decide

instance {n : Nat} (x : VarChar n) : CoeDep (VarChar n) x String where
  coe := x.val

instance (n : Nat) : ToString (VarChar n) where
  toString := VarChar.val

macro "v" x:str : term => `(VarChar.mk $x)
