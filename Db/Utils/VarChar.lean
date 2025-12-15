/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Utils.FromString

/-- A string of length bounded by `n`. -/
structure VarChar (n : Nat) where
  val : String
  length_le : val.length ≤ n := by decide

instance {n : Nat} (x : VarChar n) : CoeDep (VarChar n) x String where
  coe := x.val

instance (n : Nat) : ToString (VarChar n) where
  toString := VarChar.val

instance (n : Nat) : FromString (VarChar n) where
  fromString s := if h : s.length ≤ n then some ⟨s, h⟩ else none

macro "v" x:str : term => `(VarChar.mk $x)
