import Db.Utils.VarChar
import Db.Model.Schema

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

-- in a future version, these should be automatically generated
def Member.schema : Schema where
  name := "member"
  columns :=
    [ .mk "name" (.elementary <| .varchar 30)
    , .mk "age" (.elementary <| .int)
    , .mk "groups" (.many <| .mk "group")]
  keys := [.mk "name"]

def Group.schema : Schema where
  name := "group"
  columns :=
    [ .mk "name" (.elementary <| .varchar 20)
    , .mk "leaders" (.many <| .mk "member")]
  keys := [.mk "name"]
