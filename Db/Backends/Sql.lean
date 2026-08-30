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
  -- Named variable (e.g. as produced by an alias)
  | var (name : String)
  -- Column indexed by table and column name (printed as `table.column`)
  | column (table column : String)
  | str (s : String)
  | int (n : Int)
  | null
  deriving Repr

def Expr.toString : Expr → String
  | .true => "true"
  | .false => "false"
  | .eq e₁ e₂ => s!"({e₁.toString}) = ({e₂.toString})"
  | .and e₁ e₂ => s!"({e₁.toString}) AND ({e₂.toString})"
  | .column table col => s!"{table}.{col}"
  | .var name => name
  | .str s => s!"'{s}'"
  | .int n => ToString.toString n
  | .null => "NULL"

def Expr.fromExpr {d : Database} {view : View d} {t : DBType} : DBExpr view t → Expr
  | .true => true
  | .false => false
  | .eq e₁ e₂ => eq (fromExpr e₁) (fromExpr e₂)
  | .and e₁ e₂ => and (fromExpr e₁) (fromExpr e₂)
  | .str s => .str s.1
  | .var idx _ => .var (ToString.toString idx)

def Expr.fromName {d : Database} : d.Name → Expr
  | .ident ident => .column s!"{ident.tableName}" s!"{ident.columnName}"
  -- TODO: placeholder implementation, fix this
  | .computation name _ => .str name

inductive Selector where
  | fields (es : List (String × Expr))
  | all
  deriving Repr

def Selector.toString : Selector → String
  | .all => "*"
  | .fields fs => ", ".intercalate (fs.map <| fun f ↦ s!"{f.2.toString} as \"{f.1}\"")

inductive JoinType where
  | inner
  | outer
  deriving Repr

def JoinType.toString : JoinType → String
  | .inner => "INNER"
  | .outer => "OUTER"

inductive JoinConnect where
  | onCondition (cond : Expr)
  | usingColumn (column : String) (columns : List String)
  deriving Repr

def JoinConnect.toString : JoinConnect → String
  | .onCondition cond =>
    s!"ON {cond.toString}"
  | .usingColumn column columns =>
    s!"USING {column}{" , ".intercalate columns}"

mutual

inductive From where
  | tableName (name : String) (alias : Option String)
  | select (sel : Select) (alias : Option String)
  | join (left right : From) (joinType : JoinType) (connect : JoinConnect)
  | naturalJoin (left right : From) (joinType : JoinType)
  | crossJoin (left right : From)
  deriving Repr

structure Select where
  selector : Selector
  from_ : From
  condition : Expr
  deriving Repr

end

mutual

partial def From.toString : From → String
  | .tableName name (.some alias) =>
    s!"{name} AS {alias}"
  | .tableName name none =>
    s!"{name}"
  | .select select (.some alias) =>
    s!"( {select.toString} ) AS {alias}"
  | .select select none =>
    s!"( {select.toString} )"
  | .join left right joinType connect =>
    s!"{left.toString} {joinType.toString} {right.toString} {connect.toString}"
  | .naturalJoin left right joinType =>
    s!"{left.toString} NATURAL {joinType.toString} {right.toString}"
  | .crossJoin left right =>
    s!"{left.toString} CROSS JOIN {right.toString}"

partial def Select.toString (s : Select) : String :=
  s!"SELECT {s.selector.toString} FROM {s.from_.toString} WHERE {s.condition.toString}"

end

def Select.fromQuery {d : Database} {view : View d} (q : Query d view)
    (within : View d := view)
    (emb : view.Hom within := by exact View.Hom.id _) : Select :=
  match q with
  | .all table =>
    letI tableDef := d.tables table
    { selector :=
        .fields
          ((Enum.all tableDef.Index).toList.map fun idx : tableDef.Index ↦
            (s!"{emb.map idx}", .fromName <| (Table.view _).name idx))
      from_ := .tableName (ToString.toString table) none
      condition := .true }
  | .filter e q =>
    letI s := fromQuery q within emb
    -- TODO: the names in the condition need to be fixed
    { s with condition := .and s.condition (.fromExpr e) }
  | .join (s := view₁) (t := view₂) q₁ q₂ =>
    letI s₁ : Select := .fromQuery q₁ (view₁.prod view₂) (View.sumInl _ _)
    letI s₂ : Select := .fromQuery q₂ (view₁.prod view₂) (View.sumInr _ _)
    { selector := .all
      from_ := .crossJoin (.select s₁ none) (.select s₂ none)
      condition := .true }
  | .project (s := s) (t := view) projection query =>
    letI select : Select := .fromQuery query
    { selector :=
        .fields
          ((Enum.all view.Index).toList.map fun idx =>
            (s!"{emb.map idx}", .var s!"{projection.map idx}"))
      from_ :=
        .select select none
      condition := .true }
    ---- TODO: this also needs to fix the names to match the names used by the view
    --letI select : Select := .fromQuery query within (.comp projection emb)
    --{ selector :=
    --    .fields
    --      ((Enum.all view.Index).toList.map fun idx ↦ (s!"{emb.map idx}", .fromName <| view.name idx))
    --  from_ := select.from_
    --  condition := select.condition }

def interpretation : Interpretation Select where
  fromQuery _ := Select.fromQuery

structure Insert where
  intoTable : String
  values : List (String × Expr)

def Expr.ofDBTypeValue {t : DBType} (x : t.Value) : Expr :=
  match t with
  | .int => .int x
  | .varchar _ => .str x
  | .bool => if x then .true else .false

def Expr.ofValue {c : Column} (x : c.Value) : Expr :=
  match c, x with
  | { type := _, nullable := .false }, x => .ofDBTypeValue x
  | { type := _, nullable := .true }, some x => .ofDBTypeValue x
  | { type := _, nullable := .true }, none => .null

def Insert.fromInsert {d : Database} {tableName : d.Index} (ins : d.Insert tableName) : Insert where
  intoTable := ToString.toString tableName
  values :=
    (Enum.all (d.tables tableName).Index).toList.map
      fun colName => ⟨ToString.toString colName, .ofValue (ins.entry.value colName)⟩

def Insert.toString (ins : Insert) : String :=
  s!"INSERT INTO {ins.intoTable} ({", ".intercalate (ins.values.map Prod.fst)}) VALUES ({", ".intercalate (ins.values.map fun x => x.2.toString)})"

/-- A `DELETE` statement targeting a single table. -/
structure Delete where
  fromTable : String
  condition : Expr

def Delete.toString (del : Delete) : String :=
  s!"DELETE FROM {del.fromTable} WHERE {del.condition.toString}"

/-- Build a `DELETE` from a boolean condition over a view. SQL `DELETE` targets a single table, so
this returns `none` if the view references columns from more than one table (or from none). The
condition is translated exactly like a query filter, so column references print as bare column
names, matching `DELETE FROM <table> WHERE ...`. -/
def Delete.fromCondition {d : Database} {view : View d} (e : DBExpr view .bool) : Option Delete :=
  let tableNames : List String :=
    (Enum.all view.Index).toList.filterMap fun idx =>
      match view.name idx with
      | .ident i => some (ToString.toString i.tableName)
      | .computation .. => none
  match tableNames with
  | [] => none
  | tn :: rest => if rest.all (· == tn) then some { fromTable := tn, condition := .fromExpr e } else none

def DBType.toString : DBType → String
  | .int => "integer"
  | .varchar n => s!"varchar({n})"
  | .bool => "bool"

namespace Migration

structure FieldDef where
  name : String
  type : String
  nullable : Bool

def FieldDef.toString (fieldDef : FieldDef) : String :=
  s!"{fieldDef.name}  {fieldDef.type}{if not fieldDef.nullable then " NOT NULL" else ""}"

def FieldDef.fromColumn (column : Column) (name : String) : FieldDef where
  name := name
  type := DBType.toString column.type
  -- TODO: Technically, this is a constraint. Move to constraints?
  nullable := column.nullable

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
  fields := (Enum.all table.Index).toList.map
    fun i ↦ .fromColumn (table.columns i) (toString i)
  -- TODO: fill placeholder implementation
  constraints := []

def CreateTable.toString (cmd : CreateTable) : String :=
  letI fields : List String := cmd.fields.map FieldDef.toString
  letI constraints : List String := cmd.constraints.map ConstraintDef.toString
  s!"CREATE TABLE {cmd.tableName} (
    {",\n".intercalate fields}
    {",\n".intercalate constraints}
  )"

inductive AlterColumnCommand where
  | setType (type : String)
  | setNullable (nullable : Bool)

def AlterColumnCommand.toString : AlterColumnCommand → String
  | setType type => s!"TYPE {type}"
  | setNullable true => "DROP NOT NULL"
  | setNullable false => "SET NOT NULL"

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

def AlterTableCommand.fromTableOperation : TableOperation → List AlterTableCommand
  | .insert name col => [.addColumn (.fromColumn col name)]
  | .remove name => [.dropColumn name]
  | .rename old new => [.renameColumn old new]
  -- TODO: this is currently ignoring the `nullable` field
  | .alter name col => [
      .alterColumn name (.setType <| DBType.toString col.type),
      .alterColumn name (.setNullable <| col.nullable)
    ]

structure AlterTable where
  tableName : String
  commands : List AlterTableCommand

def AlterTable.toString (cmd : AlterTable) : String :=
  letI commands : List String := cmd.commands.map AlterTableCommand.toString
  s!"ALTER TABLE {cmd.tableName}
    {",\n".intercalate commands}
  "

def AlterTable.fromMap (tableName : String) {source target : Table}
    (map : source.Index → Option target.Index) :
    AlterTable where
  tableName := tableName
  commands := Id.run <| do
    let mut ops := []
    let mut visited : Std.HashSet target.Index := .emptyWithCapacity
    for index in Enum.all source.Index do
      match map index with
      | some val =>
        visited := visited.insert val
        if source.columns index != target.columns val then
          ops := .alterColumn s!"{val}" (.setType <| DBType.toString (target.columns val).type) :: ops
        if s!"{index}" != s!"{val}" then
          ops := .renameColumn s!"{index}" s!"{val}" :: ops
      | none =>
        ops := .dropColumn s!"{index}" :: ops
    for index in Enum.all target.Index do
      if index ∈ visited then
        continue
      ops := .addColumn (.fromColumn (target.columns index) s!"{index}") :: ops
    return ops

structure DropTable where
  tableName : String

def DropTable.toString (cmd : DropTable) : String :=
  s!"DROP TABLE {cmd.tableName}"

structure RenameTable where
  oldName : String
  newName : String

def RenameTable.toString (cmd : RenameTable) : String :=
  s!"ALTER TABLE {cmd.oldName} RENAME TO {cmd.newName}"

inductive Operation where
  | dropTable : DropTable → Operation
  | alterTable : AlterTable → Operation
  | renameTable : RenameTable → Operation
  | createTable : CreateTable → Operation

def Operation.toString : Operation → String
  | .dropTable cmd => cmd.toString
  | .createTable cmd => cmd.toString
  | .alterTable cmd => cmd.toString
  | .renameTable cmd => cmd.toString

def Operation.fromDatabaseOperation : DatabaseOperation → Operation
  | .insert name table => .createTable (.fromTable table.table name)
  | .remove name => .dropTable { tableName := name }
  | .rename old new => .renameTable { oldName := old
                                      newName := new }
  | .alter name op => .alterTable { tableName := name
                                    commands := AlterTableCommand.fromTableOperation op }

end Migration

end SQL
