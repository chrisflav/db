import Std

universe u

class Enum (α : Type u) : Type u extends Hashable α where
  [decidableEq : DecidableEq α]
  all (α) : Std.HashSet α

attribute [instance] Enum.decidableEq
