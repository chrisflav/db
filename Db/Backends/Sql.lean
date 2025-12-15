/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Interpretation.Basic

namespace SQL

inductive Expr where
  | true
  | false
  | eq (e₁ e₂ : Expr)
  | and (e₁ e₂ : Expr)
  | var (table column : String)
  | str (s : String)
  | int (n : Int)
  deriving Repr

def Expr.toString : Expr → String
  | .true => "true"
  | .false => "false"
  | .eq e₁ e₂ => s!"({e₁.toString}) = ({e₂.toString})"
  | .and e₁ e₂ => s!"({e₁.toString}) AND ({e₂.toString})"
  | .var table column => s!"{table}.{column}"
  | .str s => s!"'{s}'"
  | .int n => ToString.toString n

def Expr.fromExpr {d : Database} {t : DBType} : DBExpr d t → Expr
  | .true => true
  | .false => false
  | .eq e₁ e₂ => eq (fromExpr e₁) (fromExpr e₂)
  | .and e₁ e₂ => and (fromExpr e₁) (fromExpr e₂)
  | .str s => .str s.1
  | .var s _ => .var (ToString.toString s.tableName) (ToString.toString s.columnName)

def Expr.fromName {d : Database} : d.Name → Expr
  | .ident ident => .var (ToString.toString ident.tableName) (ToString.toString ident.columnName)
  -- TODO: placeholder implementation, fix this
  | .computation name _ => .str name

inductive Selector where
  | fields (es : List (String × Expr))
  | all
  deriving Repr

def Selector.toString : Selector → String
  | .all => "*"
  | .fields fs => ", ".intercalate (fs.map <| fun f ↦ s!"{f.2.toString} as \"{f.1}\"")

structure Select where
  selector : Selector
  fromTable : String
  condition : Expr
  -- join
  deriving Repr

def Select.toString (s : Select) : String :=
  s!"SELECT {s.selector.toString} FROM {s.fromTable} WHERE {s.condition.toString}"

def Select.fromQuery {d : Database} {names : Std.HashSet d.Name} : Query d names → Select
  | .all table =>
    { selector := .fields (names.toList.map (fun n ↦ (n.toString, .fromName n)))
      fromTable := ToString.toString table
      condition := .true }
  | .filter q e =>
    letI s := fromQuery q
    { s with condition := .and s.condition (.fromExpr e) }

def interpretation : Interpretation Select where
  fromQuery _ := Select.fromQuery

structure Insert where
  intoTable : String
  values : List (String × Expr)

def Expr.ofValue {t : DBType} (x : t.Value) : Expr :=
  match t with
  | .int => .int x
  | .varchar _ => .str x
  | .bool => if x then .true else .false

def Insert.fromInsert {d : Database} {tableName : d.Index} (ins : d.Insert tableName) : Insert where
  intoTable := ToString.toString tableName
  values :=
    (Indexing.all (d.tables tableName).Index).toList.map
      fun colName => ⟨ToString.toString colName, .ofValue (ins.values colName)⟩

def Insert.toString (ins : Insert) : String :=
  s!"INSERT INTO {ins.intoTable} ({", ".intercalate (ins.values.map Prod.fst)}) VALUES ({", ".intercalate (ins.values.map fun x => x.2.toString)})"

end SQL

section Tests

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

end Tests
