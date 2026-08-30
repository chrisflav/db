/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Interpretation.Basic
import Std.Data.HashSet.Basic

namespace SQL

inductive JoinType where
  | inner
  | outer
  deriving Repr

def JoinType.toString : JoinType → String
  | .inner => "INNER"
  | .outer => "OUTER"

mutual

/-- An untyped SQL expression. -/
inductive Expr where
  | true
  | false
  | eq (e₁ e₂ : Expr)
  | ne (e₁ e₂ : Expr)
  | lt (e₁ e₂ : Expr)
  | le (e₁ e₂ : Expr)
  | gt (e₁ e₂ : Expr)
  | ge (e₁ e₂ : Expr)
  | and (e₁ e₂ : Expr)
  | or (e₁ e₂ : Expr)
  | not (e : Expr)
  | isNull (e : Expr)
  | isNotNull (e : Expr)
  /-- `e LIKE '<pattern>' ESCAPE '\'`. -/
  | like (e : Expr) (pattern : String)
  /-- `e IN (v₁, ..., vₙ)`. -/
  | inList (e : Expr) (values : List Expr)
  /-- `e IN (SELECT ...)`. -/
  | inSelect (e : Expr) (sel : Select)
  -- Named variable (e.g. as produced by an alias)
  | var (name : String)
  -- Column indexed by table and column name (printed as `table.column`)
  | column (table column : String)
  | str (s : String)
  | int (n : Int)
  | null

inductive Selector where
  | fields (es : List (String × Expr))
  | all

inductive JoinConnect where
  | onCondition (cond : Expr)
  | usingColumn (column : String) (columns : List String)

inductive From where
  | tableName (name : String) (alias : Option String)
  | select (sel : Select) (alias : Option String)
  | join (left right : From) (joinType : JoinType) (connect : JoinConnect)
  | naturalJoin (left right : From) (joinType : JoinType)
  | crossJoin (left right : From)

structure Select where
  selector : Selector
  from_ : From
  condition : Expr

end

instance : Inhabited Expr := ⟨.null⟩
instance : Inhabited Selector := ⟨.all⟩
instance : Inhabited From := ⟨.tableName "" none⟩
instance : Inhabited Select := ⟨⟨.all, .tableName "" none, .true⟩⟩

/-- A single-quoted SQL string literal, with embedded single quotes doubled as SQL requires. -/
def quoteString (s : String) : String :=
  "'" ++ s.replace "'" "''" ++ "'"

mutual

partial def Expr.toString : Expr → String
  | .true => "true"
  | .false => "false"
  | .eq e₁ e₂ => s!"({e₁.toString}) = ({e₂.toString})"
  | .ne e₁ e₂ => s!"({e₁.toString}) <> ({e₂.toString})"
  | .lt e₁ e₂ => s!"({e₁.toString}) < ({e₂.toString})"
  | .le e₁ e₂ => s!"({e₁.toString}) <= ({e₂.toString})"
  | .gt e₁ e₂ => s!"({e₁.toString}) > ({e₂.toString})"
  | .ge e₁ e₂ => s!"({e₁.toString}) >= ({e₂.toString})"
  | .and e₁ e₂ => s!"({e₁.toString}) AND ({e₂.toString})"
  | .or e₁ e₂ => s!"({e₁.toString}) OR ({e₂.toString})"
  | .not e => s!"NOT ({e.toString})"
  | .isNull e => s!"({e.toString}) IS NULL"
  | .isNotNull e => s!"({e.toString}) IS NOT NULL"
  -- The escape character has to be given explicitly: PostgreSQL defaults to `\`, but SQLite has no
  -- default at all, so without it a pattern escaped by `DBExpr.likeEscape` would not match.
  | .like e pattern => s!"({e.toString}) LIKE {quoteString pattern} ESCAPE '\\'"
  -- `x IN ()` is a syntax error in both backends, and an empty list matches nothing.
  | .inList _ [] => "false"
  | .inList e values =>
    s!"({e.toString}) IN ({", ".intercalate (values.map Expr.toString)})"
  | .inSelect e sel => s!"({e.toString}) IN ({sel.toString})"
  | .column table col => s!"{table}.{col}"
  | .var name => name
  | .str s => quoteString s
  | .int n => ToString.toString n
  | .null => "NULL"

partial def Selector.toString : Selector → String
  | .all => "*"
  | .fields fs => ", ".intercalate (fs.map <| fun f ↦ s!"{f.2.toString} as \"{f.1}\"")

partial def JoinConnect.toString : JoinConnect → String
  | .onCondition cond =>
    s!"ON {cond.toString}"
  | .usingColumn column columns =>
    s!"USING {column}{" , ".intercalate columns}"

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

def Expr.fromName {d : Database} : d.Name → Expr
  | .ident ident => .column s!"{ident.tableName}" s!"{ident.columnName}"
  -- TODO: placeholder implementation, fix this
  | .computation name _ => .str name

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

mutual

/-- Translate a typed expression into the untyped SQL AST. A column reference is printed as its
index in the surrounding view, which is the alias `Select.fromQuery` gives it. -/
partial def Expr.fromExpr {d : Database} {view : View d} {t : DBType} : DBExpr d view t → Expr
  | .true => .true
  | .false => .false
  | .and e₁ e₂ => .and (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .or e₁ e₂ => .or (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .not e => .not (Expr.fromExpr e)
  | .eq e₁ e₂ => .eq (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .ne e₁ e₂ => .ne (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .lt e₁ e₂ => .lt (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .le e₁ e₂ => .le (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .gt e₁ e₂ => .gt (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .ge e₁ e₂ => .ge (Expr.fromExpr e₁) (Expr.fromExpr e₂)
  | .isNull e => .isNull (Expr.fromExpr e)
  | .isNotNull e => .isNotNull (Expr.fromExpr e)
  | .like e pattern _ => .like (Expr.fromExpr e) pattern
  | .inList (t := t) e values =>
    .inList (Expr.fromExpr e) (values.map (Expr.ofDBTypeValue (t := t)))
  | .inSubquery e q col _ => .inSelect (Expr.fromExpr e) (Select.column q col)
  | .str s => .str s.1
  | .int n => .int n
  | .null _ => .null
  | .var idx _ _ => .var (ToString.toString idx)

/-- The single-column `SELECT` that projects `q` onto its column `col`, as used on the right-hand
side of an `IN`. -/
partial def Select.column {d : Database} {view : View d} (q : Query d view) (col : view.Index) :
    Select where
  selector := .fields [(s!"{col}", .var s!"{col}")]
  from_ := .select (Select.fromQuery q) none
  condition := .true

partial def Select.fromQuery {d : Database} {view : View d} (q : Query d view)
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
    letI s := Select.fromQuery q within emb
    -- TODO: the names in the condition need to be fixed
    { s with condition := .and s.condition (Expr.fromExpr e) }
  | .join (s := view₁) (t := view₂) q₁ q₂ =>
    letI s₁ : Select := Select.fromQuery q₁ (view₁.prod view₂) (View.sumInl _ _)
    letI s₂ : Select := Select.fromQuery q₂ (view₁.prod view₂) (View.sumInr _ _)
    { selector := .all
      from_ := .crossJoin (.select s₁ none) (.select s₂ none)
      condition := .true }
  | .project (s := s) (t := view) projection query =>
    letI select : Select := Select.fromQuery query
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

end

def interpretation : Interpretation Select where
  fromQuery _ := Select.fromQuery

structure Insert where
  intoTable : String
  values : List (String × Expr)

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
this returns `none` unless every column of the view is a column of one and the same table.

The condition is translated exactly like a query filter, which prints a variable as its view index.
That only matches `DELETE FROM <table> WHERE ...` if the view's indices print as bare column names,
as `Table.view`'s do. A join view's indices print as `left__`/`right__` prefixed aliases, which are
only in scope inside the corresponding subquery, so such views are rejected as well. -/
def Delete.fromCondition {d : Database} {view : View d} (e : DBExpr d view .bool) :
    Option Delete := do
  let tableNames : List String ← (Enum.all view.Index).toList.mapM fun idx =>
    match view.name idx with
    | .ident i =>
      if ToString.toString idx == ToString.toString i.columnName then
        some (ToString.toString i.tableName)
      else
        none
    | .computation .. => none
  match tableNames with
  | [] => none
  | tn :: rest =>
    if rest.all (· == tn) then some { fromTable := tn, condition := .fromExpr e } else none

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
