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
  /-- An aggregate function call. `arg = none` renders as `*`, as in `COUNT(*)`. -/
  | aggregate (fn : String) (distinct : Bool) (arg : Option Expr)
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
  groupBy : List Expr := []
  orderBy : List (Expr × SortDirection) := []
  limit : Option Nat := none
  offset : Option Nat := none
  /-- Whether the selector aggregates its rows. A `WHERE` cannot be merged into such a select: it
  would be applied before the aggregation and would refer to columns the aggregate no longer has.
  Note that an aggregation without a `GROUP BY` is still one. -/
  isAggregate : Bool := false

end

instance : Inhabited Expr := ⟨.null⟩
instance : Inhabited Selector := ⟨.all⟩
instance : Inhabited From := ⟨.tableName "" none⟩
instance : Inhabited Select :=
  ⟨{ selector := .all, from_ := .tableName "" none, condition := .true }⟩

/-- A single-quoted SQL string literal, with embedded single quotes doubled as SQL requires. -/
def quoteString (s : String) : String :=
  "'" ++ s.replace "'" "''" ++ "'"

def sortDirectionToString : SortDirection → String
  | .asc => "ASC"
  | .desc => "DESC"

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
  | .aggregate fn distinct arg =>
    letI inner := match arg with
      | some e => e.toString
      | none => "*"
    s!"{fn}({if distinct then "DISTINCT " else ""}{inner})"
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
  letI groupBy :=
    if s.groupBy.isEmpty then ""
    else s!" GROUP BY {", ".intercalate (s.groupBy.map Expr.toString)}"
  letI orderBy :=
    if s.orderBy.isEmpty then ""
    else
      letI keys := s.orderBy.map fun k => s!"{k.1.toString} {sortDirectionToString k.2}"
      s!" ORDER BY {", ".intercalate keys}"
  -- SQLite rejects an `OFFSET` that is not preceded by a `LIMIT`, and PostgreSQL rejects a negative
  -- limit, so an offset without a limit is emitted with the largest limit both of them accept.
  letI limitOffset :=
    match s.limit, s.offset with
    | none, none => ""
    | some n, none => s!" LIMIT {n}"
    | some n, some m => s!" LIMIT {n} OFFSET {m}"
    | none, some m => s!" LIMIT 9223372036854775807 OFFSET {m}"
  s!"SELECT {s.selector.toString} FROM {s.from_.toString} WHERE {s.condition.toString}" ++
    s!"{groupBy}{orderBy}{limitOffset}"

end

def Expr.fromName {d : Database} : d.Name → Expr
  | .ident ident => .column s!"{ident.tableName}" s!"{ident.columnName}"
  -- A computed name is not a column of any table; it refers to the alias the query that computed
  -- it gave the value.
  | .computation name _ => .var name

def Expr.ofDBTypeValue {t : DBType} (x : t.Value) : Expr :=
  match t with
  | .int => .int x
  | .varchar _ => .str x
  | .text => .str x
  | .bool => if x then .true else .false

def Expr.ofValue {c : Column} (x : c.Value) : Expr :=
  match c, x with
  | { type := _, nullable := .false, .. }, x => .ofDBTypeValue x
  | { type := _, nullable := .true, .. }, some x => .ofDBTypeValue x
  | { type := _, nullable := .true, .. }, none => .null

/-- `s` turned into a base to hang further clauses off: a select that already limits or groups its
rows has to become a subquery first, so that a `WHERE` or a further limit applies to the rows it
produced rather than to the rows it was computed from. -/
def Select.wrap (s : Select) : Select where
  selector := .all
  from_ := .select s none
  condition := .true

/-- The expression computing one output column of an aggregate query, in terms of the aliases the
subquery holding its source rows exposes. -/
def Expr.ofAggregateEntry {d : Database} {source : View d} : AggregateEntry source → Expr
  | .group col => .var s!"{col}"
  | .countAll => .aggregate "COUNT" Bool.false none
  | .apply f col _ => .aggregate f.toString f.distinct (some (.var s!"{col}"))

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
    letI inner := Select.fromQuery q within emb
    -- A `WHERE` merged into a select that limits or groups its rows would be applied before the
    -- limit or the grouping rather than after it, so such a select becomes a subquery first.
    letI s :=
      if inner.limit.isSome || inner.offset.isSome || inner.isAggregate then inner.wrap else inner
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
  | .orderBy keys q =>
    letI inner := Select.fromQuery q within emb
    -- Sorting the rows a limit already selected is not the same as sorting before the limit.
    letI s := if inner.limit.isSome || inner.offset.isSome then inner.wrap else inner
    -- The new keys go in front of the ones already there rather than replacing them, so that
    -- sorting an already sorted query breaks its ties by the earlier sort instead of losing it.
    letI newKeys := keys.map fun k => (Expr.var s!"{emb.map k.column}", k.direction)
    { s with orderBy := newKeys ++ s.orderBy }
  | .limit n q =>
    letI inner := Select.fromQuery q within emb
    -- A second limit has to apply to the rows the first one selected.
    letI s := if inner.limit.isSome then inner.wrap else inner
    { s with limit := some n }
  | .offset n q =>
    letI inner := Select.fromQuery q within emb
    -- `LIMIT n OFFSET m` skips before it takes, so an offset applied to a query that already
    -- limits its rows would be applied in the wrong order.
    letI s := if inner.limit.isSome || inner.offset.isSome then inner.wrap else inner
    { s with offset := some n }
  | .aggregate (out := out) a q =>
    letI inner : Select := Select.fromQuery q
    { selector :=
        .fields
          ((Enum.all out.Index).toList.map fun idx =>
            (s!"{emb.map idx}", .ofAggregateEntry (a.entry idx)))
      from_ := .select inner none
      condition := .true
      groupBy := a.groupColumns.map fun col => .var s!"{col}"
      isAggregate := true }

end

def interpretation : Interpretation Select where
  fromQuery _ := Select.fromQuery

structure Insert where
  intoTable : String
  values : List (String × Expr)
  /-- The columns the statement returns, empty for one that returns nothing. -/
  returning : List String := []

def Insert.fromInsert {d : Database} {tableName : d.Index} (ins : d.Insert tableName) : Insert where
  intoTable := ToString.toString tableName
  values :=
    -- A column the insert leaves out is left out of the statement too, so that the database fills
    -- in its default.
    (Enum.all (d.tables tableName).Index).toList.filterMap
      fun colName =>
        (ins.value colName).map (fun val => (ToString.toString colName, Expr.ofValue val))

/-- The `RETURNING` clause a statement carries when it is asked for its rows.

The columns are aliased rather than returned as `*`, exactly as `Selector.toString` aliases the
columns of a `SELECT`: the databases fold an unquoted identifier to a case of their own, so a
column whose name is not already in that case would come back under a name the interpretation does
not look for. -/
def returningClause (columns : List String) : String :=
  if columns.isEmpty then ""
  else " RETURNING " ++ ", ".intercalate (columns.map fun c => s!"{c} as \"{c}\"")

/-- The names of the columns of a table, which is what a returning statement asks for. -/
def columnNames {d : Database} (tableName : d.Index) : List String :=
  (Enum.all (d.tables tableName).Index).toList.map ToString.toString

def Insert.toString (ins : Insert) : String :=
  -- An insert that supplies no column at all has to be written `DEFAULT VALUES`; the empty column
  -- and value lists are a syntax error.
  if ins.values.isEmpty then
    s!"INSERT INTO {ins.intoTable} DEFAULT VALUES{returningClause ins.returning}"
  else
    letI columns := ", ".intercalate (ins.values.map Prod.fst)
    letI values := ", ".intercalate (ins.values.map fun x => x.2.toString)
    s!"INSERT INTO {ins.intoTable} ({columns}) VALUES ({values})" ++
      returningClause ins.returning

/-- An `UPDATE` statement targeting a single table. -/
structure Update where
  table : String
  /-- The columns to set, and what to set them to. -/
  assignments : List (String × Expr)
  condition : Expr
  /-- The columns the statement returns, empty for one that returns nothing. -/
  returning : List String := []

def Update.toString (upd : Update) : String :=
  letI sets := ", ".intercalate (upd.assignments.map fun a => s!"{a.1} = {a.2.toString}")
  s!"UPDATE {upd.table} SET {sets} WHERE {upd.condition.toString}" ++
    returningClause upd.returning

def Update.fromUpdate {d : Database} {tableName : d.Index} (upd : d.Update tableName) : Update where
  table := ToString.toString tableName
  assignments :=
    (Enum.all (d.tables tableName).Index).toList.filterMap
      fun colName =>
        (upd.value colName).map (fun e => (ToString.toString colName, Expr.fromExpr e))
  condition := .fromExpr upd.condition

/-- A `DELETE` statement targeting a single table. -/
structure Delete where
  fromTable : String
  condition : Expr
  /-- The columns the statement returns, empty for one that returns nothing. -/
  returning : List String := []

def Delete.toString (del : Delete) : String :=
  s!"DELETE FROM {del.fromTable} WHERE {del.condition.toString}" ++
    returningClause del.returning

def Delete.fromDelete {d : Database} {tableName : d.Index} (del : d.Delete tableName) :
    Delete where
  fromTable := ToString.toString tableName
  condition := .fromExpr del.condition

def DBType.toString : DBType → String
  | .int => "integer"
  | .varchar n => s!"varchar({n})"
  | .text => "text"
  | .bool => "bool"

/-- A column default, as it is written in a `CREATE TABLE`. A call is parenthesised, which SQLite
requires and PostgreSQL accepts. -/
def ColumnDefault.toString : ColumnDefault → String
  | .int n => ToString.toString n
  | .str s => quoteString s
  | .bool true => "true"
  | .bool false => "false"
  | .null => "NULL"
  | .call fn => s!"({fn})"

/-- Whether `s` is a single-quoted SQL string literal, i.e. every quote inside it is doubled. This
is what tells a literal apart from an expression that merely begins and ends with a quote, such as
`'a' || 'b'`, which matters because SQLite reports an expression default with its parentheses
already stripped. -/
def isQuotedLiteral (s : String) : Bool :=
  s.length ≥ 2 && s.startsWith "'" && s.endsWith "'" &&
    !(((s.drop 1).dropEnd 1).replace "''" "").contains '\''

/--
Parse a column default back from the SQL text a database reports for it. The type of the column
disambiguates the literals that several types spell the same way, such as `0`.

Anything that is not a literal of the column's type is an expression, since that is what the
databases report for one: SQLite strips the parentheses a call was declared with, and PostgreSQL
casts and constant-folds what it reports. Two expression defaults compare equal, so recognising one
as an expression is all that is needed of it.
-/
def ColumnDefault.parse? (t : DBType) (raw : String) : Option ColumnDefault :=
  letI s := raw.trimAscii.toString
  letI unquoted? : Option String :=
    if isQuotedLiteral s then some (((s.drop 1).dropEnd 1).replace "''" "'") else none
  letI asCall : Option ColumnDefault :=
    if s.startsWith "(" && s.endsWith ")" then
      -- Parenthesised, as `ColumnDefault.toString` writes a call.
      some (.call ((s.drop 1).dropEnd 1).trimAscii.toString)
    else
      some (.call s)
  if s.isEmpty then
    none
  else if s.toUpper == "NULL" then
    some .null
  else
    match t with
    -- A literal of a non-character type can be reported quoted: PostgreSQL reports a declared
    -- `DEFAULT -1` as `'-1'::integer`.
    | .int =>
      match (unquoted?.getD s).toInt? with
      | some n => some (.int n)
      | none => asCall
    | .bool =>
      match (unquoted?.getD s).toUpper with
      | "TRUE" => some (.bool true)
      | "FALSE" => some (.bool false)
      | "1" => some (.bool true)
      | "0" => some (.bool false)
      | _ => asCall
    | .varchar _ | .text =>
      match unquoted? with
      | some literal => some (.str literal)
      | none => asCall

/-- Strip the explicit type cast PostgreSQL appends to the column default it reports, e.g. the
`::character varying` of `'open'::character varying`.

Only a cast of the whole expression is stripped. A cast inside a call, as in the
`abs('-1'::integer)` PostgreSQL reports for a declared `abs(-1)`, is part of the call and has to
stay: cutting the expression there would leave an unbalanced fragment. -/
def stripCast (s : String) : String := Id.run do
  let cs := s.toList
  let mut inQuote := false
  let mut depth := 0
  let mut cut : Option Nat := none
  let mut i := 0
  for c in cs do
    if inQuote then
      -- A doubled quote inside a literal toggles twice, which leaves the state correct.
      inQuote := c != '\''
    else if c == '\'' then
      inQuote := true
    else if c == '(' then
      depth := depth + 1
    else if c == ')' then
      depth := depth - 1
    else if c == ':' && depth == 0 && cs[i + 1]? == some ':' then
      cut := some i
    i := i + 1
  match cut with
  | some n => return (s.take n).trimAscii.toString
  | none => return s

/-- The SQL dialect a statement is rendered in. The two backends spell an auto-incrementing
primary key differently, and nothing else in this module depends on the dialect. -/
inductive Dialect where
  | postgres
  | sqlite
  deriving Repr, BEq, DecidableEq

namespace Migration

structure FieldDef where
  name : String
  type : String
  nullable : Bool
  default? : Option ColumnDefault := none
  /-- Whether the database assigns this column's value. -/
  autoIncrement : Bool := false

def FieldDef.toString (dialect : Dialect) (fieldDef : FieldDef) : String :=
  if fieldDef.autoIncrement then
    match dialect with
    -- SQLite only auto-increments a column declared exactly `INTEGER PRIMARY KEY`, and declares
    -- the key inline; `CreateTable.toString` therefore omits the separate `PRIMARY KEY` clause.
    | .sqlite => s!"{fieldDef.name}  INTEGER PRIMARY KEY AUTOINCREMENT"
    | .postgres => s!"{fieldDef.name}  {fieldDef.type} NOT NULL GENERATED BY DEFAULT AS IDENTITY"
  else
    letI dflt := match fieldDef.default? with
      | some d => s!" DEFAULT {ColumnDefault.toString d}"
      | none => ""
    s!"{fieldDef.name}  {fieldDef.type}{if not fieldDef.nullable then " NOT NULL" else ""}{dflt}"

def FieldDef.fromColumn (column : Column) (name : String) : FieldDef where
  name := name
  type := DBType.toString column.type
  -- TODO: Technically, this is a constraint. Move to constraints?
  nullable := column.nullable
  default? := column.default?
  autoIncrement := column.autoIncrement

structure CreateTable where
  tableName : String
  fields : List FieldDef
  primaryKey : List String := []
  unique : List (List String) := []
  foreignKeys : List (ForeignKey String) := []

def CreateTable.fromTable (table : Table) (name : String) : CreateTable where
  tableName := name
  fields := (Enum.all table.Index).toList.map
    fun i ↦ .fromColumn (table.columns i) (toString i)
  primaryKey := table.primaryKey.map toString
  unique := table.unique.map fun group => group.map toString
  foreignKeys := table.foreignKeys.map (ForeignKey.map toString)

def CreateTable.fromRecipe (recipe : TableRecipe) (name : String) : CreateTable where
  tableName := name
  fields := recipe.columns.toList.map fun (n, c) => .fromColumn c n
  primaryKey := recipe.primaryKey
  unique := recipe.unique
  foreignKeys := recipe.foreignKeys

/-- The columns of `cmd` whose value the database generates. -/
def CreateTable.generated (cmd : CreateTable) : List FieldDef :=
  cmd.fields.filter (·.autoIncrement)

/--
Whether SQLite declares the primary key of `cmd` inline, on the generated column itself.

It only auto-increments a column declared exactly `INTEGER PRIMARY KEY`, so this holds precisely
when there is one generated column and it is the whole primary key. `CreateTable.sqliteError?`
rejects every other shape, rather than emitting a table with a key nobody asked for.
-/
def CreateTable.inlineKey (dialect : Dialect) (cmd : CreateTable) : Bool :=
  match dialect, cmd.generated with
  | .sqlite, [field] => cmd.primaryKey == [field.name]
  | _, _ => false

/-- Why SQLite cannot create this table, if it cannot. -/
def CreateTable.sqliteError? (cmd : CreateTable) : Option String :=
  match cmd.generated with
  | [] => none
  | [field] =>
    if cmd.primaryKey == [field.name] then none
    else
      some <|
        s!"table `{cmd.tableName}` declares the generated column `{field.name}`, but its " ++
        s!"primary key is `{", ".intercalate cmd.primaryKey}`. SQLite only generates the value " ++
        "of a column that is exactly `INTEGER PRIMARY KEY`, so the two have to coincide."
  | fields =>
    some <|
      s!"table `{cmd.tableName}` declares more than one generated column " ++
      s!"({", ".intercalate (fields.map (·.name))}). SQLite allows at most one, and it has " ++
      "to be the primary key."

def CreateTable.toString (dialect : Dialect) (cmd : CreateTable) : String :=
  letI fields : List String := cmd.fields.map (FieldDef.toString dialect)
  -- Where SQLite declares the key inline it must not be declared a second time.
  letI inlineKey := cmd.inlineKey dialect
  letI primaryKey : List String :=
    if cmd.primaryKey.isEmpty || inlineKey then []
    else [s!"PRIMARY KEY ({", ".intercalate cmd.primaryKey})"]
  letI unique : List String := cmd.unique.map fun group =>
    s!"UNIQUE ({", ".intercalate group})"
  letI foreignKeys : List String := cmd.foreignKeys.map fun fk =>
    s!"FOREIGN KEY ({", ".intercalate fk.columns}) " ++
      s!"REFERENCES {fk.foreignTable} ({", ".intercalate fk.foreignColumns}) " ++
      s!"ON DELETE {fk.onDelete.sql} ON UPDATE {fk.onUpdate.sql}"
  letI entries := fields ++ primaryKey ++ unique ++ foreignKeys
  s!"CREATE TABLE {cmd.tableName} (\n  {",\n  ".intercalate entries}\n)"

inductive AlterColumnCommand where
  | setType (type : String)
  | setNullable (nullable : Bool)
  | setDefault (default? : Option ColumnDefault)

def AlterColumnCommand.toString : AlterColumnCommand → String
  | setType type => s!"TYPE {type}"
  | setNullable true => "DROP NOT NULL"
  | setNullable false => "SET NOT NULL"
  | setDefault (some d) => s!"SET DEFAULT {ColumnDefault.toString d}"
  | setDefault none => "DROP DEFAULT"

inductive AlterTableCommand where
  | addColumn (field : FieldDef)
  | dropColumn (name : String)
  | renameColumn (oldName newName : String)
  | alterColumn (name : String) (cmd : AlterColumnCommand)

def AlterTableCommand.toString (dialect : Dialect) : AlterTableCommand → String
  | addColumn field => s!"ADD COLUMN {field.toString dialect}"
  | renameColumn oldName newName => s!"RENAME COLUMN {oldName} TO {newName}"
  | alterColumn name cmd => s!"ALTER COLUMN {name} {cmd.toString}"
  | dropColumn name => s!"DROP COLUMN {name}"

def AlterTableCommand.fromTableOperation : TableOperation → List AlterTableCommand
  | .insert name col => [.addColumn (.fromColumn col name)]
  | .remove name => [.dropColumn name]
  | .rename old new => [.renameColumn old new]
  | .alter name col => [
      .alterColumn name (.setType <| DBType.toString col.type),
      .alterColumn name (.setNullable <| col.nullable),
      .alterColumn name (.setDefault col.default?)
    ]

structure AlterTable where
  tableName : String
  commands : List AlterTableCommand

def AlterTable.toString (dialect : Dialect) (cmd : AlterTable) : String :=
  letI commands : List String := cmd.commands.map (AlterTableCommand.toString dialect)
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
          ops := .alterColumn s!"{val}"
            (.setType <| DBType.toString (target.columns val).type) :: ops
          ops := .alterColumn s!"{val}" (.setNullable (target.columns val).nullable) :: ops
          ops := .alterColumn s!"{val}" (.setDefault (target.columns val).default?) :: ops
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

def Operation.toString (dialect : Dialect) : Operation → String
  | .dropTable cmd => cmd.toString
  | .createTable cmd => cmd.toString dialect
  | .alterTable cmd => cmd.toString dialect
  | .renameTable cmd => cmd.toString

def Operation.fromDatabaseOperation : DatabaseOperation → Operation
  | .insert name table => .createTable (.fromRecipe table name)
  | .remove name => .dropTable { tableName := name }
  | .rename old new => .renameTable { oldName := old
                                      newName := new }
  | .alter name op => .alterTable { tableName := name
                                    commands := AlterTableCommand.fromTableOperation op }

end Migration

end SQL
