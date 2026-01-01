/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Interpretation.Basic
import Std.Data.HashSet.Basic

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
      fun colName => ⟨ToString.toString colName, .ofValue (ins.entry.values colName)⟩

def Insert.toString (ins : Insert) : String :=
  s!"INSERT INTO {ins.intoTable} ({", ".intercalate (ins.values.map Prod.fst)}) VALUES ({", ".intercalate (ins.values.map fun x => x.2.toString)})"

def DBType.toString : DBType → String
  | .int => "integer"
  | .varchar n => s!"varchar({n})"
  | .bool => "bool"

namespace Migration

structure FieldDef where
  name : String
  type : String

def FieldDef.toString (fieldDef : FieldDef) : String :=
  s!"{fieldDef.name}  {fieldDef.type}"

def FieldDef.fromColumn (column : Column) (name : String) : FieldDef where
  name := name
  type := DBType.toString column.type

-- TODO: fill placeholder implementation
structure ConstraintDef where
  name : String

def ConstraintDef.toString (constraintDef : ConstraintDef) : String :=
  s!"{constraintDef.name}"

structure CreateTable where
  tableName : String
  fields : List FieldDef
  constraints : List ConstraintDef

def CreateTable.fromTable (table : Table) (name : String) : CreateTable where
  tableName := name
  fields := (Indexing.all table.Index).toList.map
    fun i ↦ .fromColumn (table.columns i) (toString i)
  -- TODO: fill placeholder implementation
  constraints := []

def CreateTable.toString (cmd : CreateTable) : String :=
  letI fields : List String := cmd.fields.map FieldDef.toString
  letI constraints : List String := cmd.constraints.map ConstraintDef.toString
  s!"CREATE TABLE {cmd.tableName}
    {"\n,".intercalate fields}
    {"\n,".intercalate constraints}
  )"

inductive AlterColumnCommand where
  | setType (type : String)

def AlterColumnCommand.toString : AlterColumnCommand → String
  | setType type => s!"TYPE {type}"

inductive AlterTableCommand where
  | addColumn (field : FieldDef)
  | dropColumn (name : String)
  | renameColumn (oldName newName : String)
  | alterColumn (name : String) (cmd : AlterColumnCommand)

def AlterTableCommand.toString : AlterTableCommand → String
  | addColumn field => s!"ADD COLUMN {field.toString}"
  | renameColumn oldName newName => s!"RENAME COLUMN {oldName} TO {newName}"
  | alterColumn name cmd => s!"ALTER COLUMN {name} {cmd.toString}"
  | dropColumn name => s!"DROP COLUMN {name}"

structure AlterTable where
  tableName : String
  commands : List AlterTableCommand

def AlterTable.toString (cmd : AlterTable) : String :=
  letI commands : List String := cmd.commands.map AlterTableCommand.toString
  s!"ALTER TABLE {cmd.tableName}
    {"\n,".intercalate commands}
  "

def AlterTable.fromMap (tableName : String) {source target : Table}
    (map : source.Index → Option target.Index) :
    AlterTable where
  tableName := tableName
  commands := Id.run <| do
    let mut ops := []
    let mut visited : Std.HashSet target.Index := .emptyWithCapacity
    for index in Indexing.all source.Index do
      match map index with
      | some val =>
        visited := visited.insert val
        if s!"{index}" != s!"{val}" then
          ops := .renameColumn s!"{index}" s!"{val}" :: ops
        if source.columns index != target.columns val then
          ops := .alterColumn s!"{val}" (.setType <| DBType.toString (target.columns val).type) :: ops
      | none =>
        ops := .dropColumn s!"{index}" :: ops
    return ops

end Migration

end SQL
