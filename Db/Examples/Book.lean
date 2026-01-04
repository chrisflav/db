/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

namespace BookExample

structure Author where
  name : VarChar 100
  age : Int
  retired : Bool
  deriving Repr

generate_table BookExample.Author

inductive Index where
  | author
  deriving DecidableEq, Hashable, Repr, Enum

instance : ToString Index where
  toString
    | .author => "author"

instance : FromString Index where
  fromString
    | "author" => some .author
    | _ => none

instance : Indexing Index where

def database : Database where
  Index := Index
  tables
    | .author => AuthorTable

instance : HasTable Author (database.tables .author) :=
  inferInstanceAs <| HasTable Author AuthorTable

def authorModel : Model database Author where
  index := .author

end BookExample
