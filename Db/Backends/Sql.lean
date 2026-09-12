/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Interpretation.Basic
import Db.Backends.Dialect
import Std.Data.HashSet.Basic

namespace SQL

inductive JoinType where
  | inner
  | outer
  | leftOuter
  deriving Repr

/-- Includes the `JOIN` itself, so that `NATURAL {this}` and `{left} {this} {right}` both come out
as the SQL they mean. `OUTER JOIN` on its own is not a join either database accepts. -/
def JoinType.toString : JoinType → String
  | .inner => "INNER JOIN"
  | .outer => "FULL OUTER JOIN"
  | .leftOuter => "LEFT OUTER JOIN"

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
  /-- A subquery used as a value, which is what a `SELECT` list needs it to be. -/
  | scalar (sel : Select)
  /-- An aggregate function call. `arg = none` renders as `*`, as in `COUNT(*)`. -/
  | aggregate (fn : String) (distinct : Bool) (arg : Option Expr)
  -- Named variable (e.g. as produced by an alias)
  | var (name : String)
  -- Column indexed by table and column name (printed as `table.column`)
  | column (table column : String)
  | str (s : String)
  | int (n : Int)
  | add (e₁ e₂ : Expr)
  | sub (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
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

structure OrderKey where
  expr : Expr
  direction : SortDirection := .asc
  collation : Collation := .binary
  nulls : NullsOrder := .default

structure Select where
  selector : Selector
  from_ : From
  condition : Expr
  groupBy : List Expr := []
  orderBy : List OrderKey := []
  limit : Option Nat := none
  offset : Option Nat := none
  /-- Whether the selector aggregates its rows. A `WHERE` cannot be merged into such a select: it
  would be applied before the aggregation and would refer to columns the aggregate no longer has.
  Note that an aggregation without a `GROUP BY` is still one. -/
  isAggregate : Bool := false
  /-- The common table expressions this statement declares, rendered as its `WITH` clause.

  They belong to the statement and not to the query that needed one: `WITH` is only legal at the
  top of a statement, so every combinator hoists the CTEs of its operands (see `Translation.ctes`)
  and only the outermost `Select` renders them. `Query.recursive` is what produces one. -/
  ctes : List CTE := []

/-- A common table expression: `name AS (base)`, or `name AS (base UNION ALL step)` for a recursive
one, whose `step` is evaluated over the rows found so far and reaches them by naming `name`. -/
structure CTE where
  name : String
  /-- Whether `step` may name this CTE, which is what `WITH RECURSIVE` declares. -/
  recursive : Bool := false
  base : Select
  /-- The recursive step, absent for a plain CTE. -/
  step : Option Select := none

end

instance : Inhabited Expr := ⟨.null⟩
instance : Inhabited Selector := ⟨.all⟩
instance : Inhabited From := ⟨.tableName "" none⟩
instance : Inhabited Select :=
  ⟨{ selector := .all, from_ := .tableName "" none, condition := .true }⟩
instance : Inhabited CTE := ⟨{ name := "", base := default }⟩

/-- Whether this `FROM` is itself a join, which decides whether it needs parentheses as the right
operand of another one. -/
def From.isJoin : From → Bool
  | .join .. | .naturalJoin .. | .crossJoin .. => true
  | .tableName .. | .select .. => false

/-- The SQL text comparing `sql` under `collation`.

A case-insensitive comparison is `lower(...)` rather than a declared collation because the two
backends have no collation in common: SQLite's is `NOCASE`, and PostgreSQL has none that is
case-insensitive without an ICU collation being created first. `lower` is in both, means the same
ASCII folding SQLite's `NOCASE` does, and — being an ordinary expression — is something both can
build an index on, which is what makes an index declared this way usable by an `ORDER BY` written
the same way. -/
def collated : Collation → String → String
  | .binary, sql => sql
  | .caseInsensitive, sql => s!"lower({sql})"

/-- A single-quoted SQL string literal, with embedded single quotes doubled as SQL requires. -/
def quoteString (s : String) : String :=
  "'" ++ s.replace "'" "''" ++ "'"

/-- A double-quoted SQL identifier, with embedded double quotes doubled.

Quoting is what keeps the identifier's case on PostgreSQL, which folds an unquoted one to lower
case while SQLite keeps it as written — so a column declared `createdAt` came back from PostgreSQL
introspection as `createdat`, and `autoUpdate` proposed to add it again on every run. It is also
what lets a reserved word (`order`, `select`, `user`) be a name at all. Both backends spell a
quoted identifier the same way, so this needs no dialect. -/
def quoteIdent (s : String) : String :=
  "\"" ++ s.replace "\"" "\"\"" ++ "\""

/-- A possibly schema-qualified relation name, `schema.table`, quoted one component at a time.

Quoting the whole of `information_schema.columns` as one identifier would name a table whose name
contains a dot rather than the catalogue view; that catalogue is the one place inside the library
where a qualified name occurs. The cost is that a table whose own name contains a dot cannot be
named — a dotted name is always read as `schema.table`. -/
def quoteQualified (s : String) : String :=
  ".".intercalate ((s.splitOn ".").map quoteIdent)

def sortDirectionToString : SortDirection → String
  | .asc => "ASC"
  | .desc => "DESC"

/-- Where a sort puts its `NULL`s, if it says at all. Both backends spell this the same way, and
have since SQLite 3.30. -/
def nullsOrderToString : NullsOrder → String
  | .default => ""
  | .first => " NULLS FIRST"
  | .last => " NULLS LAST"

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
  | .scalar sel => s!"({sel.toString})"
  | .aggregate fn distinct arg =>
    letI inner := match arg with
      | some e => e.toString
      | none => "*"
    s!"{fn}({if distinct then "DISTINCT " else ""}{inner})"
  | .column table col => s!"{quoteQualified table}.{quoteIdent col}"
  | .var name => quoteIdent name
  | .str s => quoteString s
  | .int n => ToString.toString n
  | .add e₁ e₂ => s!"({e₁.toString}) + ({e₂.toString})"
  | .sub e₁ e₂ => s!"({e₁.toString}) - ({e₂.toString})"
  | .mul e₁ e₂ => s!"({e₁.toString}) * ({e₂.toString})"
  | .null => "NULL"

partial def Selector.toString : Selector → String
  | .all => "*"
  | .fields fs => ", ".intercalate (fs.map <| fun f ↦ s!"{f.2.toString} as {quoteIdent f.1}")

partial def JoinConnect.toString : JoinConnect → String
  | .onCondition cond =>
    s!"ON {cond.toString}"
  -- `USING` takes a parenthesised, comma-separated list, and its entries are column names like any
  -- other. The first column is a separate field only so that the list cannot be empty, which SQL
  -- would not accept.
  | .usingColumn column columns =>
    s!"USING ({", ".intercalate ((column :: columns).map quoteIdent)})"

partial def From.toString : From → String
  | .tableName name (.some alias) =>
    s!"{quoteQualified name} AS {quoteIdent alias}"
  | .tableName name none =>
    s!"{quoteQualified name}"
  | .select select (.some alias) =>
    s!"( {select.toString} ) AS {quoteIdent alias}"
  | .select select none =>
    s!"( {select.toString} )"
  -- A right operand that is itself a join is parenthesised: joins associate to the left, so
  -- `a LEFT OUTER JOIN b CROSS JOIN c ON p` reads as `(a LEFT OUTER JOIN b) CROSS JOIN c` and the
  -- `ON` then belongs to the wrong join — a misparse where it is not outright an error. A left
  -- operand needs no parentheses for the same reason. Both backends accept a parenthesised joined
  -- table as an operand.
  | .join left right joinType connect =>
    s!"{left.toString} {joinType.toString} {From.parenthesised right} {connect.toString}"
  | .naturalJoin left right joinType =>
    s!"{left.toString} NATURAL {joinType.toString} {From.parenthesised right}"
  | .crossJoin left right =>
    s!"{left.toString} CROSS JOIN {From.parenthesised right}"

/-- A `FROM` as it is written in the right-hand operand position of a join. -/
partial def From.parenthesised (f : From) : String :=
  if f.isJoin then s!"({f.toString})" else f.toString

/-- `name AS (base)`, or `name AS (base UNION ALL step)` for a recursive one. The `RECURSIVE`
keyword is not here but on the `WITH`, which is where SQL puts it. -/
partial def CTE.toString (c : CTE) : String :=
  letI body :=
    match c.step with
    | some step => s!"{c.base.toString} UNION ALL {step.toString}"
    | none => c.base.toString
  s!"{quoteIdent c.name} AS ({body})"

partial def Select.toString (s : Select) : String :=
  letI groupBy :=
    if s.groupBy.isEmpty then ""
    else s!" GROUP BY {", ".intercalate (s.groupBy.map Expr.toString)}"
  letI orderBy :=
    if s.orderBy.isEmpty then ""
    else
      letI keys := s.orderBy.map fun k =>
        s!"{collated k.collation k.expr.toString} {sortDirectionToString k.direction}" ++
          nullsOrderToString k.nulls
      s!" ORDER BY {", ".intercalate keys}"
  -- SQLite rejects an `OFFSET` that is not preceded by a `LIMIT`, and PostgreSQL rejects a negative
  -- limit, so an offset without a limit is emitted with the largest limit both of them accept.
  letI limitOffset :=
    match s.limit, s.offset with
    | none, none => ""
    | some n, none => s!" LIMIT {n}"
    | some n, some m => s!" LIMIT {n} OFFSET {m}"
    | none, some m => s!" LIMIT 9223372036854775807 OFFSET {m}"
  -- `RECURSIVE` is declared for the whole `WITH` rather than per CTE, which is how both backends
  -- spell it, and it is harmless on a list whose CTEs happen not to recur.
  letI with_ :=
    if s.ctes.isEmpty then ""
    else
      letI recursive := if s.ctes.any (·.recursive) then "RECURSIVE " else ""
      s!"WITH {recursive}{", ".intercalate (s.ctes.map CTE.toString)} "
  s!"{with_}SELECT {s.selector.toString} FROM {s.from_.toString} WHERE {s.condition.toString}" ++
    s!"{groupBy}{orderBy}{limitOffset}"

end

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

/-- The conjunction of two conditions, with a `true` operand dropped.

`.true` is the condition a translation that filters nothing carries, and the combinators conjoin
the conditions of their operands as they merge them, so a plain three-way join would otherwise come
out as `WHERE (((true) AND (true)) AND (true)) AND (...)` — noise that hides the condition the
query actually has. Folded here rather than in `Expr.toString`, which stays a printer: it renders
the expression it is given, and a `.and .true e` a caller built on purpose is still printed as
written. -/
def Expr.conj : Expr → Expr → Expr
  | .true, e => e
  | e, .true => e
  | e₁, e₂ => .and e₁ e₂

/-- The translation of a `Query d view`: a `FROM` with the clauses that go with it, and for every
column of `view` the SQL expression computing it *in the scope of that `FROM`*.

This is what makes joins flat. The alternative, which this replaces, was to materialise every
scope as a subquery whose `SELECT` list renamed the columns to the aliases of the enclosing view,
so that a condition could name them; every operand of a join was then a `FROM ( SELECT ... )`.
Keeping the expressions instead means nothing has to be renamed until the very top, where
`toSelect` names each column once, by its alias in `view`. -/
structure Translation {d : Database} (view : View d) where
  from_ : From
  condition : Expr := .true
  /-- The expression computing each output column, in the scope of `from_`. -/
  column : view.Index → Expr
  groupBy : List Expr := []
  orderBy : List OrderKey := []
  limit : Option Nat := none
  offset : Option Nat := none
  isAggregate : Bool := false
  /-- The common table expressions this query needs. They are hoisted through every combinator to
  the enclosing statement, which is the only place a `WITH` may stand. `Query.recursive` is what
  produces one. -/
  ctes : List CTE := []

instance {d : Database} {view : View d} : Inhabited (Translation view) :=
  ⟨{ from_ := default, column := fun _ => default }⟩

/-- The alias for the next occurrence of a table (or of a subquery) in the statement being built.

Every occurrence gets one, so that a table joined with itself stays distinguishable and so that a
correlated subquery can name an outer column unambiguously. All references go through these
aliases, so a user table that happens to be called `t1` is no problem: it comes out as
`"t1" AS "t3"`. -/
def fresh : StateM Nat String := do
  let n ← modifyGet fun n => (n, n + 1)
  return s!"t{n + 1}"

/-- The translation as a statement of its own: the columns are given their names in `view`, which
is what the backends decode rows by. -/
def Translation.toSelect {d : Database} {view : View d} (t : Translation view) : Select where
  selector := .fields ((Enum.all view.Index).toList.map fun i => (view.alias i, t.column i))
  from_ := t.from_
  condition := t.condition
  groupBy := t.groupBy
  orderBy := t.orderBy
  limit := t.limit
  offset := t.offset
  isAggregate := t.isAggregate
  ctes := t.ctes

/-- Whether a clause that selects rows — a `WHERE`, a `LIMIT`, an `OFFSET` — can be merged into
this translation. It cannot once the translation limits, offsets or aggregates its rows: the
clause would then apply to the rows the translation was computed *from* rather than to the ones it
produced. An `ORDER BY` survives all of these, so it does not count here. -/
def Translation.isFlat {d : Database} {view : View d} (t : Translation view) : Bool :=
  t.limit.isNone && t.offset.isNone && !t.isAggregate && t.groupBy.isEmpty

/-- Whether this translation can be an operand of a join as it stands. Beyond `isFlat` that needs
its `ORDER BY` to be empty: the keys of a join operand would end up ordering the join, which is not
what the operand asked for. -/
def Translation.isJoinable {d : Database} {view : View d} (t : Translation view) : Bool :=
  t.isFlat && t.orderBy.isEmpty

/-- Whether every output column is a bare reference to a column of `from_` rather than something
computed from one.

This is what decides whether a translation may be the right-hand operand of a left outer join as
it stands. Such a join has to produce `NULL` in *every* right-hand column for a left row that finds
no partner, and only a column reference does that by itself: `Query.extend` and `Query.correlate`
leave an expression behind, and that expression is evaluated per row of the join, not per row of
the right-hand relation. So `a ⟕ (b extended by 5)` would hand an unmatched row of `a` the value
`5`, and `a ⟕ (b with a correlated COUNT(*))` a count of `0`, where the view — which makes every
right-hand column nullable — says `NULL`. Wrapped in a subquery the columns become references to
it, and the join nulls them out as it should. -/
def Translation.readsColumns {d : Database} {view : View d} (t : Translation view) : Bool :=
  (Enum.all view.Index).toList.all fun i =>
    match t.column i with
    | .column .. => Bool.true
    | _ => Bool.false

/-- Whether this translation can stand as one branch of the `UNION ALL` of a recursive common
table expression as it stands.

`ORDER BY`, `LIMIT` and `OFFSET` belong to the compound statement rather than to one of its
branches, so a branch carrying one has to become a subquery first; written out where it stands,
SQLite rejects it (`LIMIT clause should come after UNION ALL not before`) and PostgreSQL reports a
syntax error at the `UNION`. A `GROUP BY` needs no wrap: a grouped select is an ordinary branch of
a compound statement, whatever the databases then think of a recursive query that aggregates. -/
def Translation.isUnionBranch {d : Database} {view : View d} (t : Translation view) : Bool :=
  t.limit.isNone && t.offset.isNone && t.orderBy.isEmpty

/-- `t` as a subquery, for a clause that cannot be merged into it. Its columns are then reached by
their alias in `view` through the subquery's own alias.

The alias is not optional: a subquery in a `FROM` without one is a syntax error on PostgreSQL 15
and older. The CTEs are hoisted out rather than rendered on the nested select, a `WITH` being legal
only at the top of a statement. -/
def Translation.wrap {d : Database} {view : View d} (t : Translation view) :
    StateM Nat (Translation view) := do
  let a ← fresh
  return { from_ := .select { t.toSelect with ctes := [] } (some a)
           column := fun i => .column a (view.alias i)
           ctes := t.ctes }

/-- `t` wrapped if it is not flat, and as it is otherwise. -/
def Translation.flatten {d : Database} {view : View d} (t : Translation view) :
    StateM Nat (Translation view) :=
  if t.isFlat then pure t else t.wrap

/-- `t` wrapped if it cannot be a join operand as it stands, and as it is otherwise. -/
def Translation.joinable {d : Database} {view : View d} (t : Translation view) :
    StateM Nat (Translation view) :=
  if t.isJoinable then pure t else t.wrap

/-- `t` wrapped if it cannot be the right-hand operand of a left outer join as it stands, and as
it is otherwise. Beyond being a join operand at all that needs `readsColumns`, so that the join
can null-extend every one of its columns. -/
def Translation.nullExtendable {d : Database} {view : View d} (t : Translation view) :
    StateM Nat (Translation view) :=
  if t.isJoinable && t.readsColumns then pure t else t.wrap

/-- `t` wrapped if it cannot be a branch of a `UNION ALL` as it stands, and as it is otherwise. -/
def Translation.unionBranch {d : Database} {view : View d} (t : Translation view) :
    StateM Nat (Translation view) :=
  if t.isUnionBranch then pure t else t.wrap

mutual

/-- Translate a typed expression into the untyped SQL AST, in the environment `env` that says how
each column of the view is computed in the scope the expression will stand in. -/
partial def Expr.fromExpr {d : Database} {view : View d} {t : DBType}
    (env : view.Index → Expr) : DBExpr d view t → StateM Nat Expr
  | .true => pure .true
  | .false => pure .false
  | .and e₁ e₂ => return .and (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .or e₁ e₂ => return .or (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .not e => return .not (← Expr.fromExpr env e)
  | .eq e₁ e₂ => return .eq (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .ne e₁ e₂ => return .ne (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .lt e₁ e₂ => return .lt (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .le e₁ e₂ => return .le (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .gt e₁ e₂ => return .gt (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .ge e₁ e₂ => return .ge (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .isNull e => return .isNull (← Expr.fromExpr env e)
  | .isNotNull e => return .isNotNull (← Expr.fromExpr env e)
  | .like e pattern _ => return .like (← Expr.fromExpr env e) pattern
  | .inList (t := t) e values =>
    return .inList (← Expr.fromExpr env e) (values.map (Expr.ofDBTypeValue (t := t)))
  | .inSubquery e q col _ => return .inSelect (← Expr.fromExpr env e) (← Select.column q col)
  | .add e₁ e₂ => return .add (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .sub e₁ e₂ => return .sub (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .mul e₁ e₂ => return .mul (← Expr.fromExpr env e₁) (← Expr.fromExpr env e₂)
  | .str s => pure (.str s.1)
  | .int n => pure (.int n)
  | .null _ => pure .null
  | .var idx _ _ => pure (env idx)

/-- The single-column `SELECT` that projects `q` onto its column `col`, as used on the right-hand
side of an `IN`. No nesting: every clause of `q` is kept, only the `SELECT` list is narrowed.

This is the one place a CTE would not be hoisted to the enclosing statement — the result is an
`Expr`, which has nowhere to hoist to — so it renders its own `WITH`, which both backends accept
inside a subquery expression. -/
partial def Select.column {d : Database} {view : View d} (q : Query d view) (col : view.Index) :
    StateM Nat Select := do
  let t ← translate q
  return { t.toSelect with selector := .fields [(view.alias col, t.column col)] }

/-- Translate a query into a `FROM` with its clauses and one expression per output column.

Each case merges what it can into the translation it is given and wraps it in a subquery only when
it cannot; the comments say which is which. -/
partial def translate {d : Database} {view : View d} (q : Query d view) :
    StateM Nat (Translation view) := do
  match q with
  | .all table =>
    -- Every table occurrence is aliased, so that a table joined with itself has two names.
    let a ← fresh
    return { from_ := .tableName (ToString.toString table) (some a)
             column := fun i => .column a ((Table.view table).alias i) }
  | .filter e q =>
    let t ← (← translate q).flatten
    -- The condition is translated in the source's own environment, so a filter on a column an
    -- `extend` or a `correlate` computed names that computation rather than an alias of the same
    -- `SELECT` list — which PostgreSQL does not have in scope in a `WHERE`.
    let c ← Expr.fromExpr t.column e
    return { t with condition := Expr.conj t.condition c }
  | .join q₁ q₂ =>
    let t₁ ← (← translate q₁).joinable
    let t₂ ← (← translate q₂).joinable
    return { from_ := .crossJoin t₁.from_ t₂.from_
             condition := Expr.conj t₁.condition t₂.condition
             column := Sum.elim t₁.column t₂.column
             ctes := t₁.ctes ++ t₂.ctes }
  | .leftJoin q₁ q₂ on =>
    let t₁ ← (← translate q₁).joinable
    -- The right-hand side has to be one the join can null-extend, which is more than being a join
    -- operand: see `Translation.readsColumns`.
    let t₂ ← (← translate q₂).nullExtendable
    let env := Sum.elim t₁.column t₂.column
    let onExpr ← Expr.fromExpr env on
    -- The right-hand side's own filter goes into the `ON`, not into the `WHERE`:
    -- `a ⟕ σ_p(b)` is `a ⟕ b ON (on ∧ p)`, whereas a `WHERE p` would run after the join had
    -- already null-extended the unmatched left rows and would then delete exactly those rows. The
    -- left-hand side's filter does belong in the `WHERE`: it selects rows of `a`, which the join
    -- keeps either way.
    return { from_ :=
               .join t₁.from_ t₂.from_ .leftOuter (.onCondition (Expr.conj onExpr t₂.condition))
             condition := t₁.condition
             column := env
             ctes := t₁.ctes ++ t₂.ctes }
  | .project p q =>
    -- A projection renames and drops output columns, which only the `SELECT` list at the top ever
    -- sees, so it generates no SQL at all: it just re-indexes the column expressions.
    let t ← translate q
    return { from_ := t.from_
             condition := t.condition
             column := fun i => t.column (p.map i)
             groupBy := t.groupBy
             orderBy := t.orderBy
             limit := t.limit
             offset := t.offset
             isAggregate := t.isAggregate
             ctes := t.ctes }
  | .orderBy keys q =>
    let t ← translate q
    -- Sorting the rows a limit already selected is not the same as sorting before the limit.
    let t ← if t.limit.isSome || t.offset.isSome then t.wrap else pure t
    -- The new keys go in front of the ones already there rather than replacing them, so that
    -- sorting an already sorted query breaks its ties by the earlier sort instead of losing it.
    let newKeys := keys.map fun k =>
      ({ expr := t.column k.column, direction := k.direction, collation := k.collation,
         nulls := k.nulls } : OrderKey)
    return { t with orderBy := newKeys ++ t.orderBy }
  | .limit n q =>
    let t ← translate q
    -- A second limit has to apply to the rows the first one selected.
    let t ← if t.limit.isSome then t.wrap else pure t
    return { t with limit := some n }
  | .offset n q =>
    let t ← translate q
    -- `LIMIT n OFFSET m` skips before it takes, so an offset applied to a query that already
    -- limits its rows would be applied in the wrong order.
    let t ← if t.limit.isSome || t.offset.isSome then t.wrap else pure t
    return { t with offset := some n }
  | .aggregate (out := out) a q =>
    let t ← translate q
    -- Beyond the reasons `isFlat` gives, an inner `ORDER BY` forces the wrap too: ordering rows
    -- before grouping them means nothing, and once the grouping were merged in, PostgreSQL would
    -- reject the keys outright as columns that are neither grouped nor aggregated.
    let t ← t.joinable
    return { from_ := t.from_
             -- The filter of the source runs before the grouping, which is what filtering the
             -- rows an aggregate aggregates means.
             condition := t.condition
             column := fun i =>
               match a.entry i with
               | .group c => t.column c
               | .countAll => .aggregate "COUNT" Bool.false none
               | .apply f c _ => .aggregate f.toString f.distinct (some (t.column c))
             groupBy := a.groupColumns.map t.column
             isAggregate := true
             ctes := t.ctes }
  | .extend name _ e q =>
    -- A computed column never needs a wrap: it changes no row set, and an expression over the
    -- source's column expressions is a legal `SELECT` list entry wherever they are — over an
    -- aggregate select list included, where it becomes an expression over the aggregates.
    let t ← translate q
    let value ← Expr.fromExpr t.column e
    return { t with column := Sum.elim t.column (fun _ => value) }
  | .correlate name q sub on agg _ =>
    -- A scalar subquery correlated with a row of an aggregate is not a thing: the outer row is a
    -- group, and the condition would name columns the grouping no longer has.
    let t ← translate q
    let t ← if t.isAggregate || !t.groupBy.isEmpty then t.wrap else pure t
    let s ← (← translate sub).joinable
    -- The outer columns are `"t1"."name"` references, and are in scope inside the scalar subquery
    -- because every alias in the statement is distinct — which is what makes the correlation work
    -- without either side being renamed.
    let onExpr ← Expr.fromExpr (Sum.elim t.column s.column) on
    let aggExpr : Expr :=
      match agg with
      | .group col => s.column col
      | .countAll => .aggregate "COUNT" Bool.false none
      | .apply f col _ => .aggregate f.toString f.distinct (some (s.column col))
    let scalar : Select :=
      { selector := .fields [(name, aggExpr)]
        from_ := s.from_
        condition := Expr.conj s.condition onExpr
        isAggregate := true }
    return { t with
             column := Sum.elim t.column (fun _ => .scalar scalar)
             ctes := t.ctes ++ s.ctes }
  | .cteRef name view =>
    -- A reference to a relation the enclosing statement declares, which stands in a `FROM` just as
    -- a table does. Its columns carry the aliases of `view`, because the CTE's body is rendered by
    -- `toSelect`, which is what names them so.
    let a ← fresh
    return { from_ := .tableName name (some a)
             column := fun i => .column a (view.alias i) }
  | .recursive (view := view) name base step =>
    -- A branch that orders, limits or offsets its rows becomes a subquery first: those clauses
    -- belong to the compound statement and not to one of its branches, so written out where they
    -- stand both backends reject the statement. See `Translation.isUnionBranch`.
    let b ← (← translate base).unionBranch
    let s ← (← translate step).unionBranch
    -- The two bodies are statements of their own, so the CTEs they need are hoisted out of them
    -- and declared next to this one rather than inside it, a `WITH` being legal only at the top of
    -- a statement. They go first, so that a CTE a body depends on is declared before it.
    let cte : CTE :=
      { name := name
        recursive := true
        base := { b.toSelect with ctes := [] }
        step := some { s.toSelect with ctes := [] } }
    -- What the query denotes is the CTE's rows, which is a reference to it — the same `FROM` and
    -- the same column expressions `.cteRef` builds, with the declaration carried along.
    let a ← fresh
    return { from_ := .tableName name (some a)
             column := fun i => .column a (view.alias i)
             ctes := b.ctes ++ s.ctes ++ [cte] }

end

/-- The `SELECT` statement computing `q`: the translation of `q`, with its columns named by their
aliases in `view`, which is what the backends decode rows by. -/
def Select.fromQuery {d : Database} {view : View d} (q : Query d view) : Select :=
  ((translate q).run' 0).toSelect

def interpretation : Interpretation Select where
  fromQuery _ := Select.fromQuery

/-- What an insert does with a row that conflicts with one already stored. -/
inductive ConflictClause where
  | error
  | ignore
  | update (target : List String) (set : List String)

/-- The `ON CONFLICT` clause, which both backends spell the same way — SQLite has had it since
3.24, so its own `INSERT OR IGNORE` is not needed and one spelling serves both. The one place that
does not hold is an insert with no columns, where SQLite lets nothing follow `DEFAULT VALUES`;
`Insert.toString` handles that case itself and does not come here.

`DO UPDATE` with nothing to set is `DO NOTHING`: an update that assigns no column is not a
statement, and doing nothing is what it would have amounted to. -/
def ConflictClause.toString : ConflictClause → String
  | .error => ""
  | .ignore => " ON CONFLICT DO NOTHING"
  | .update _ [] => " ON CONFLICT DO NOTHING"
  | .update target set =>
    -- `excluded` names the row the statement could not store, not anything anybody declared, so
    -- it is the one name here that stays bare.
    letI assignments :=
      ", ".intercalate (set.map fun c => s!"{quoteIdent c} = excluded.{quoteIdent c}")
    s!" ON CONFLICT ({", ".intercalate (target.map quoteIdent)}) DO UPDATE SET {assignments}"

structure Insert where
  intoTable : String
  values : List (String × Expr)
  /-- The columns the statement returns, empty for one that returns nothing. -/
  returning : List String := []
  /-- What to do with a row that conflicts with one already stored. -/
  onConflict : ConflictClause := .error

def Insert.fromInsert {d : Database} {tableName : d.Index} (ins : d.Insert tableName) : Insert where
  intoTable := ToString.toString tableName
  values :=
    -- A column the insert leaves out is left out of the statement too, so that the database fills
    -- in its default.
    (Enum.all (d.tables tableName).Index).toList.filterMap
      fun colName =>
        (ins.value colName).map (fun val => (ToString.toString colName, Expr.ofValue val))
  onConflict :=
    match ins.onConflict with
    | .error => .error
    | .ignore => .ignore
    | .update target set => .update (target.map ToString.toString) (set.map ToString.toString)

/-- The `RETURNING` clause a statement carries when it is asked for its rows.

The columns are listed and aliased rather than returned as `*`, exactly as `Selector.toString`
aliases the columns of a `SELECT`, so that the statement states the name each value comes back
under instead of leaving it to the backend. Now that the column reference is quoted the alias
repeats a name the database would have used anyway, but it also fixes the order the columns come
back in, which `*` leaves to the table's own column order. -/
def returningClause (columns : List String) : String :=
  if columns.isEmpty then ""
  else
    " RETURNING " ++
      ", ".intercalate (columns.map fun c => s!"{quoteIdent c} as {quoteIdent c}")

/-- The names of the columns of a table, which is what a returning statement asks for. -/
def columnNames {d : Database} (tableName : d.Index) : List String :=
  (Enum.all (d.tables tableName).Index).toList.map ToString.toString

/-- Why SQLite cannot run this insert, if it cannot.

SQLite parses `ON CONFLICT` only after a `VALUES` or a `SELECT`, never after `DEFAULT VALUES`, so
an insert that supplies no column and resolves its conflicts by updating has no spelling there at
all: `INSERT OR REPLACE` deletes the conflicting row and inserts a new one rather than assigning
the listed columns of the old one, which is a different statement. Reported rather than rendered
into SQL the database would reject, and rather than silently run as something else. -/
def Insert.sqliteError? (ins : Insert) : Option String :=
  match ins.values.isEmpty, ins.onConflict with
  | true, .update _ (_ :: _) =>
    some <|
      s!"the insert into `{ins.intoTable}` supplies no column, so it has to be written " ++
      "`DEFAULT VALUES`, and SQLite accepts no `ON CONFLICT ... DO UPDATE` after that. Supply " ++
      "at least one column, or use `.ignore`."
  | _, _ => none

/-- The statement, in `dialect`.

The dialect is needed only for an insert that supplies no column: `DEFAULT VALUES` followed by
`ON CONFLICT DO NOTHING` is a syntax error on SQLite (`near "ON"`) and accepted by PostgreSQL, so
SQLite gets its own `INSERT OR IGNORE` for that one case. The two are not the same statement in
general — `OR IGNORE` skips a row violating any constraint, `DO NOTHING` only one violating a
uniqueness constraint — but a row that supplies no column at all has nothing to violate a `CHECK`
or a `NOT NULL` with that its defaults do not already decide. -/
def Insert.toString (dialect : Dialect) (ins : Insert) : String :=
  -- An insert that supplies no column at all has to be written `DEFAULT VALUES`; the empty column
  -- and value lists are a syntax error.
  if ins.values.isEmpty then
    letI ignoring :=
      dialect == .sqlite &&
        match ins.onConflict with
        | .ignore => Bool.true
        | .update _ [] => Bool.true
        | _ => Bool.false
    letI conflict := if ignoring then "" else ins.onConflict.toString
    s!"INSERT {if ignoring then "OR IGNORE " else ""}INTO {quoteQualified ins.intoTable} " ++
      s!"DEFAULT VALUES{conflict}" ++ returningClause ins.returning
  else
    letI columns := ", ".intercalate (ins.values.map fun x => quoteIdent x.1)
    letI values := ", ".intercalate (ins.values.map fun x => x.2.toString)
    s!"INSERT INTO {quoteQualified ins.intoTable} ({columns}) VALUES ({values})" ++
      ins.onConflict.toString ++ returningClause ins.returning

/-- An `UPDATE` statement targeting a single table. -/
structure Update where
  table : String
  /-- The columns to set, and what to set them to. -/
  assignments : List (String × Expr)
  condition : Expr
  /-- The columns the statement returns, empty for one that returns nothing. -/
  returning : List String := []

def Update.toString (upd : Update) : String :=
  letI sets :=
    ", ".intercalate (upd.assignments.map fun a => s!"{quoteIdent a.1} = {a.2.toString}")
  s!"UPDATE {quoteQualified upd.table} SET {sets} WHERE {upd.condition.toString}" ++
    returningClause upd.returning

/-- The environment a statement that writes one table translates its expressions in: a column is
the bare, unqualified name the table declares. An `UPDATE` or a `DELETE` names exactly one table
and gives it no alias, so there is nothing to qualify the name with. -/
def tableEnv {d : Database} (tableName : d.Index) : (Table.view tableName).Index → Expr :=
  fun i => .var ((Table.view tableName).alias i)

def Update.fromUpdate {d : Database} {tableName : d.Index} (upd : d.Update tableName) : Update :=
  -- One alias counter for the whole statement, so that two assignments that each contain a
  -- subquery do not both call their table `t1`.
  let go : StateM Nat Update := do
    let env := tableEnv tableName
    let assignments ← (Enum.all (d.tables tableName).Index).toList.foldlM
      (fun (acc : Array (String × Expr)) colName =>
        match upd.value colName with
        | some e => return acc.push (ToString.toString colName, ← Expr.fromExpr env e)
        | none => pure acc)
      #[]
    return { table := ToString.toString tableName
             assignments := assignments.toList
             condition := ← Expr.fromExpr env upd.condition }
  go.run' 0

/-- A `DELETE` statement targeting a single table. -/
structure Delete where
  fromTable : String
  condition : Expr
  /-- The columns the statement returns, empty for one that returns nothing. -/
  returning : List String := []

def Delete.toString (del : Delete) : String :=
  s!"DELETE FROM {quoteQualified del.fromTable} WHERE {del.condition.toString}" ++
    returningClause del.returning

def Delete.fromDelete {d : Database} {tableName : d.Index} (del : d.Delete tableName) :
    Delete where
  fromTable := ToString.toString tableName
  condition := (Expr.fromExpr (tableEnv tableName) del.condition).run' 0

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
    | .sqlite => s!"{quoteIdent fieldDef.name}  INTEGER PRIMARY KEY AUTOINCREMENT"
    | .postgres =>
      s!"{quoteIdent fieldDef.name}  {fieldDef.type} NOT NULL GENERATED BY DEFAULT AS IDENTITY"
  else
    letI dflt := match fieldDef.default? with
      | some d => s!" DEFAULT {ColumnDefault.toString d}"
      | none => ""
    -- The type is not an identifier: `varchar(20)` quoted would name a type nobody declared.
    s!"{quoteIdent fieldDef.name}  {fieldDef.type}" ++
      s!"{if not fieldDef.nullable then " NOT NULL" else ""}{dflt}"

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
    else [s!"PRIMARY KEY ({", ".intercalate (cmd.primaryKey.map quoteIdent)})"]
  letI unique : List String := cmd.unique.map fun group =>
    s!"UNIQUE ({", ".intercalate (group.map quoteIdent)})"
  letI foreignKeys : List String := cmd.foreignKeys.map fun fk =>
    s!"FOREIGN KEY ({", ".intercalate (fk.columns.map quoteIdent)}) " ++
      s!"REFERENCES {quoteQualified fk.foreignTable} " ++
      s!"({", ".intercalate (fk.foreignColumns.map quoteIdent)}) " ++
      s!"ON DELETE {fk.onDelete.sql} ON UPDATE {fk.onUpdate.sql}"
  letI entries := fields ++ primaryKey ++ unique ++ foreignKeys
  s!"CREATE TABLE {quoteQualified cmd.tableName} (\n  {",\n  ".intercalate entries}\n)"

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
  | renameColumn oldName newName =>
    s!"RENAME COLUMN {quoteIdent oldName} TO {quoteIdent newName}"
  | alterColumn name cmd => s!"ALTER COLUMN {quoteIdent name} {cmd.toString}"
  | dropColumn name => s!"DROP COLUMN {quoteIdent name}"

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
  s!"ALTER TABLE {quoteQualified cmd.tableName}
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
  s!"DROP TABLE {quoteQualified cmd.tableName}"

structure RenameTable where
  oldName : String
  newName : String

/-- The new name is a bare table name rather than a qualified one: `RENAME TO` moves no table
between schemas, so a dot in it would be part of the name rather than a separator. -/
def RenameTable.toString (cmd : RenameTable) : String :=
  s!"ALTER TABLE {quoteQualified cmd.oldName} RENAME TO {quoteIdent cmd.newName}"

/-- The SQL text of one key of an index: the column under its collation, then its direction. -/
def indexKeyToString (key : IndexKey String) : String :=
  s!"{collated key.collation (quoteIdent key.column)} {sortDirectionToString key.direction}"

structure CreateIndex where
  indexName : String
  tableName : String
  keys : List (IndexKey String)
  unique : Bool := false

/-- Both backends spell this the same way, expression keys included, so this takes no dialect. -/
def CreateIndex.toString (cmd : CreateIndex) : String :=
  letI keys := ", ".intercalate (cmd.keys.map indexKeyToString)
  s!"CREATE {if cmd.unique then "UNIQUE " else ""}INDEX {quoteIdent cmd.indexName} " ++
    s!"ON {quoteQualified cmd.tableName} ({keys})"

structure DropIndex where
  indexName : String

def DropIndex.toString (cmd : DropIndex) : String :=
  s!"DROP INDEX {quoteIdent cmd.indexName}"

/-- The statement one index operation is. -/
def indexOperationToString : IndexOperation → String
  | .create table index =>
    CreateIndex.toString
      { indexName := index.name, tableName := table, keys := index.keys, unique := index.unique }
  | .drop _ name => DropIndex.toString { indexName := name }

/-! ### Reading an index back

Both backends store an index as the text of its `CREATE INDEX`, and neither reports its keys in a
structured form an expression key survives: SQLite's `pragma_index_xinfo` gives `NULL` for the
column of an expression key, and PostgreSQL has no per-key view at all. So the text is parsed back,
which is tractable because the only text this has to understand is the text `CreateIndex.toString`
produces — modulo the canonicalisation PostgreSQL applies to it when handing it back.

The parsing works on `List Char` throughout: it is short, and it keeps the slice-returning string
API out of code whose whole job is taking text apart.
-/

/-- Drop leading and trailing spaces. -/
private def trimChars (cs : List Char) : List Char :=
  cs.dropWhile (·.isWhitespace) |>.reverse |>.dropWhile (·.isWhitespace) |>.reverse

/-- Split on commas that are not inside parentheses. -/
private partial def splitTopLevelAux :
    List Char → Nat → List Char → List (List Char) → List (List Char)
  | [], _, cur, acc => (cur.reverse :: acc).reverse
  | c :: rest, depth, cur, acc =>
    if c == '(' then splitTopLevelAux rest (depth + 1) (c :: cur) acc
    else if c == ')' then splitTopLevelAux rest (depth - 1) (c :: cur) acc
    else if c == ',' && depth == 0 then splitTopLevelAux rest depth [] (cur.reverse :: acc)
    else splitTopLevelAux rest depth (c :: cur) acc

/-- The text between the last balanced pair of parentheses, which for an index DDL is its key
list. -/
private def lastParenGroup? (cs : List Char) : Option (List Char) := Id.run do
  let mut close : Option Nat := none
  for i in [0:cs.length] do
    if cs[i]! == ')' then close := some i
  let some closeIdx := close | return none
  let mut depth : Nat := 0
  for i in [0:closeIdx + 1] do
    let j := closeIdx - i
    if cs[j]! == ')' then depth := depth + 1
    else if cs[j]! == '(' then
      depth := depth - 1
      if depth == 0 then
        return some ((cs.drop (j + 1)).take (closeIdx - j - 1))
  return none

/-- Whether `cs` ends with `suffix`, ignoring case. -/
private def endsWithCI (cs : List Char) (suffix : String) : Bool :=
  letI s := suffix.toList.map Char.toLower
  cs.length ≥ s.length && (cs.drop (cs.length - s.length)).map Char.toLower == s

/-- Whether `cs` ends with `suffix` as a word of its own, i.e. with whitespace in front of it.

A plain `endsWithCI` is not enough for the keywords of a key: PostgreSQL reports an ascending key
without the `ASC` it was declared with, so the whole of such a key's text is the column name, and
`endsWithCI ... "asc"` then takes the tail off a column called `basc` (and `"desc"` off one called
`recdesc`). The index would be read back over a column the table does not have, and `autoUpdate`
would drop and re-create it on every run instead of converging. -/
private def endsWithWordCI (cs : List Char) (suffix : String) : Bool :=
  endsWithCI cs suffix &&
    match cs[cs.length - suffix.length - 1]? with
    | some c => c.isWhitespace
    | none => false

/-- Whether `cs` starts with `prefix'`, ignoring case. -/
private def startsWithCI (cs : List Char) (prefix' : String) : Bool :=
  letI s := prefix'.toList.map Char.toLower
  cs.length ≥ s.length && (cs.take s.length).map Char.toLower == s

/-- Undo the doubling `quoteIdent` applies to the double quotes inside an identifier.

Only inside the quotes: this is the inverse of what `quoteIdent` wrote, so it is applied exactly
where the quotes have just been stripped. -/
private def undoubleQuotes : List Char → List Char
  | '"' :: '"' :: rest => '"' :: undoubleQuotes rest
  | c :: rest => c :: undoubleQuotes rest
  | [] => []

/-- Strip what a database adds around a column reference when it reports an expression back:
surrounding parentheses, a `::text` cast, and double quotes around the identifier — the last of
which also undoes the doubling of the quotes inside, or the name read back is not the name that
was declared and `autoUpdate` re-creates the index on every run instead of converging. -/
private partial def normalizeIdent (cs : List Char) : List Char :=
  letI t := trimChars cs
  if endsWithCI t "::text" then normalizeIdent (t.take (t.length - 6))
  else if t.length ≥ 2 && t.head? == some '(' && t.getLast? == some ')' then
    normalizeIdent (t.drop 1 |>.take (t.length - 2))
  else if t.length ≥ 2 && t.head? == some '"' && t.getLast? == some '"' then
    undoubleQuotes (t.drop 1 |>.take (t.length - 2))
  else t

/-- Parse one key of an index DDL: a column or `lower(column)`, then an optional direction. -/
private def parseIndexKey? (cs : List Char) : Option (IndexKey String) := Id.run do
  let mut text := trimChars cs
  let mut direction := SortDirection.asc
  -- PostgreSQL reports the null placement the direction already implies; it says nothing extra.
  for suffix in ["nulls first", "nulls last"] do
    if endsWithWordCI text suffix then
      text := trimChars (text.take (text.length - suffix.length))
  if endsWithWordCI text "desc" then
    direction := .desc
    text := trimChars (text.take (text.length - 4))
  else if endsWithWordCI text "asc" then
    text := trimChars (text.take (text.length - 3))
  if startsWithCI text "lower(" && text.getLast? == some ')' then
    let inner := normalizeIdent (text.drop 6 |>.take (text.length - 7))
    if inner.isEmpty then return none
    return some
      { column := String.ofList inner, direction := direction, collation := .caseInsensitive }
  let column := normalizeIdent text
  if column.isEmpty then return none
  return some { column := String.ofList column, direction := direction, collation := .binary }

/-- Parse an index back out of the `CREATE INDEX` text a backend reports for it.

`name` is passed in rather than read out of the text: both backends already know it, and it is the
one part whose spelling they disagree on (PostgreSQL quotes and schema-qualifies it). -/
def parseCreateIndex? (name : String) (sql : String) : Option (TableIndex String) := do
  let cs := sql.toList
  let keys ← lastParenGroup? cs
  let parsed := (splitTopLevelAux keys 0 [] []).filterMap parseIndexKey?
  if parsed.isEmpty then none
  else
    -- Only the `UNIQUE` before `INDEX` counts; a column called `unique_something` does not.
    let isUnique := startsWithCI (trimChars cs) "create unique index"
    some { name := name, keys := parsed, unique := isUnique }

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
