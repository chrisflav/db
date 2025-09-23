/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Utils.VarChar

mutual

/-- A group has a name and a list of organizers, called leaders. -/
structure Group where
  name : VarChar 20
  leaders : Array Member

/-- A member has a name and an age and a list of groups it is a member of. -/
structure Member where
  name : VarChar 30
  age : Nat
  groups : Array Group

end

def leaders : Group where
  name := v"Leaders"
  leaders := #[]

def peter : Member where
  name := v"Peter"
  age := 42
  groups := #[leaders]
