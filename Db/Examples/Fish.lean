/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

inductive FishIndex where
  | name
  | length
  deriving DecidableEq, Hashable, Repr

instance : ToString FishIndex where
  toString
    | .name => "name"
    | .length => "length"

instance : FromString FishIndex where
  fromString
    | "name" => some .name
    | "length" => some .length
    | _ => none

instance : Indexing FishIndex where
  all := {.name, .length}
  fromString_toString x := by induction x <;> rfl

abbrev fish : Table where
  Index := FishIndex
  columns
    | .name => ⟨.varchar 100⟩
    | .length => ⟨.int⟩

inductive DatabaseIndex where
  | fish
  deriving DecidableEq, Hashable, Repr

instance : ToString DatabaseIndex where
  toString
    | .fish => "fish"

instance : FromString DatabaseIndex where
  fromString
    | "fish" => some .fish
    | _ => none

instance : Indexing DatabaseIndex where
  all := {.fish}
  fromString_toString x := by induction x <;> rfl

abbrev database : Database where
  Index := DatabaseIndex
  tables
    | .fish => fish

def nameIdent : database.Ident where
  tableName := .fish
  columnName := .length
  column := ⟨.int⟩

example : nameIdent.dbtype = .int := rfl

example : nameIdent.dbtype.Value := (3 : Int)

def q := SQL.Select.fromQuery (d := database) (.filter (.all DatabaseIndex.fish)
  (.eq (.var nameIdent (.varchar 100)) (.str ⟨"Swordfish", by decide⟩)))

def ins : SQL.Insert where
  intoTable := "fish"
  values := [⟨"name", .str "Aal"⟩, ⟨"length", .int 56⟩]

def ins2 : SQL.Insert :=
  SQL.Insert.fromInsert (d := database) (tableName := .fish)
    { values
        | .name => ⟨"Aal", by decide⟩
        | .length => 56 }
