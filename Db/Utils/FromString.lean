universe u

class FromString (α : Type u) where
  fromString : String → Option α

instance : FromString Int where
  fromString := String.toInt?

instance : FromString Nat where
  fromString := String.toNat?

instance : FromString Bool where
  fromString
    | "true" => some true
    | "True" => some true
    | "false" => some false
    | "False" => some false
    | "t" => some true
    | "f" => some false
    | "1" => some true
    | "0" => some false
    | "YES" => some true
    | "NO" => some false
    | _ => none

instance : FromString String where
  fromString := some
