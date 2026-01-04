/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Init.Data.Function
import Db

namespace FishExample

inductive FishIndex where
  | name
  | length
  deriving DecidableEq, Hashable, Repr, Enum

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

abbrev fish : Table where
  Index := FishIndex
  columns
    | .name => ⟨.varchar 100, false⟩
    | .length => ⟨.int, false⟩

inductive DatabaseIndex where
  | fish
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString DatabaseIndex where
  toString
    | .fish => "fish"

instance : FromString DatabaseIndex where
  fromString
    | "fish" => some .fish
    | _ => none

instance : Indexing DatabaseIndex where

abbrev database : Database where
  Index := DatabaseIndex
  tables
    | .fish => fish

def nameIdent : database.Ident where
  tableName := .fish
  columnName := .length
  column := ⟨.int, false⟩

example : nameIdent.dbtype = .int := rfl

example : nameIdent.dbtype.Value := (3 : Int)

def q := SQL.Select.fromQuery (d := database) (.filter (.all DatabaseIndex.fish)
  (.eq (.var nameIdent (.varchar 100)) (.str ⟨"Swordfish", by decide⟩)))

def ins : SQL.Insert where
  intoTable := "fish"
  values := [⟨"name", .str "Aal"⟩, ⟨"length", .int 56⟩]

def ins2 : SQL.Insert :=
  SQL.Insert.fromInsert (d := database) (tableName := .fish)
    { entry.values
        | .name => ⟨"Aal", by decide⟩
        | .length => 56 }

example : String :=
  SQL.Migration.CreateTable.toString (.fromTable fish "fish")

inductive Fish2Index where
  | name
  | river
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString Fish2Index where
  toString
    | .name => "title"
    | .river => "river"

instance : FromString Fish2Index where
  fromString
    | "title" => some .name
    | "river" => some .river
    | _ => none

instance : Indexing Fish2Index where

def fish2 : Table where
  Index := Fish2Index
  columns
    | .name =>
      { type := .varchar 50
        nullable := false }
    | .river =>
      { type := .bool
        nullable := false }

def fishToFish2 : FishIndex → Option Fish2Index
  | .name => some .name
  | .length => none

def alterTable : SQL.Migration.AlterTable :=
  .fromMap "fish" (source := fish) (target := fish2) fishToFish2

structure Fish where
  name : VarChar 100
  length : Int

def Fish.toEntry (f : Fish) : fish.Entry where
  values
    | .name => f.name
    | .length => f.length

def Fish.fromEntry (e : fish.Entry) : Fish where
  name := e.values .name
  length := e.values .length

structure Many (α : Type) : Type where

class HasKey (α : Type) where
  Key : Type
  key : α → Key
  -- key_injective {x y : α} (h : key x = key y) : x = y

export HasKey (Key)

structure Person where
  id : Int
  name : VarChar 50
  age : Int

instance : HasKey Person where
  Key := Int
  key := Person.id

structure Lake where
  name : VarChar 50
  fish : Many Fish
  owner : Key Person

end FishExample
