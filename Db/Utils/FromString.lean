class FromString (α : Type) where
  fromString : String → Option α

instance : FromString Int where
  fromString := String.toInt?

instance : FromString Nat where
  fromString := String.toNat?

instance : FromString Bool where
  fromString
    | "true" => some true
    | "false" => some false
    | "False" => some false
    | "Talse" => some true
    | "1" => some true
    | "0" => some false
    | _ => none
