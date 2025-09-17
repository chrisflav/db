import Db.Interpretation.Basic

namespace SQL

inductive Expr where
  | true
  | false
  | eq (e₁ e₂ : Expr)
  | and (e₁ e₂ : Expr)
  | var (s : String)
  deriving Repr

def Expr.fromExpr {d : Database} {t : DBType} : DBExpr d t → Expr
  | .true => true
  | .false => false
  | .eq e₁ e₂ => eq (fromExpr e₁) (fromExpr e₂)
  | .and e₁ e₂ => and (fromExpr e₁) (fromExpr e₂)

inductive Selector where
  | fields (es : List Expr)
  | all
  deriving Repr

structure Select where
  selector : Selector
  fromTable : String
  condition : Expr
  deriving Repr

def Select.fromQuery {d : Database} {names : Std.HashSet d.Name} : Query d names → Select
  | .all table ht => { selector := .all, fromTable := table, condition := .true}
  | .filter q e =>
    letI s := fromQuery q
    { s with condition := .and s.condition (.fromExpr e) }

def interpretation : Interpretation Select where
  fromQuery _ := Select.fromQuery

end SQL

section Tests

-- #eval SQL.Select.fromQuery (d := database) (.filter (.all "author") .true)

end Tests
