/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

namespace SQL

inductive Expr where
  | true
  | false
  | eq (e₁ e₂ : Expr)
  | and (e₁ e₂ : Expr)
  | var (table column : String)
  | str (s : String)
  | int (n : Int)
  | null
  deriving Repr

def Expr.toString : Expr → String
  | .true => "true"
  | .false => "false"
  | .eq e₁ e₂ => s!"({e₁.toString}) = ({e₂.toString})"
  | .and e₁ e₂ => s!"({e₁.toString}) AND ({e₂.toString})"
  | .var table column => s!"{table}.{column}"
  | .str s => s!"'{s}'"
  | .int n => ToString.toString n
  | .null => "NULL"

mutual

inductive JoinType where
  | inner
  | outer

inductive JoinConnect where
  | onCondition (cond : Expr)
  | usingColumn (column : String) (columns : List String)

inductive From where
  | tableName (name : String) (alias : String)
  | select (sel : Select) (alias : String)
  | join (left right : From) (joinType : JoinType) (connect : JoinConnect)
  | naturalJoin (left right : From) (joinType : JoinType)
  | crossJoin (left right : From)

inductive Selector where
  | all
  | expressions (l : Expr) (alias : String)

structure Select where
  selector : List (Selector)
  «from» : List From
  «where» : Option Expr

end

end SQL
