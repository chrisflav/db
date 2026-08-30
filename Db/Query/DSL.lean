/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Query.Basic
import Db.Model.HasTable

/-!
# A type-safe query DSL

This module implements a `do`-style surface syntax for building `QuerySet`s over types that
have a `HasModel` (and hence `HasView`) instance:

```
query% do
  let b ← from Book
  let a ← from Author
  guard b.author = a.name
  guard a.retired
  select b
```

The block above elaborates to a term of type `QuerySet Book`. Each `let x ← from T` cross joins
the table backing `T`, each `guard c` adds a filter and `select x` projects the result onto the
columns of `x`.

Each `let x ← from T` introduces a genuine local variable `x : T`, exactly as if it had been
fetched from the database in an ordinary `do` block. Inside the block the editor therefore offers
the full interactive experience: hovering over `x` shows its type, dot-completion after `x.`
suggests the fields of `T`, "go to definition" works, and ill-typed comparisons are reported by
Lean's own elaborator. The `guard`/`select` clauses are elaborated as ordinary terms in this
context and are then translated into the `Query`/`DBExpr`/`View` core.
-/

open Lean Elab Term Meta

namespace Db.Query.DSL

/-- A single statement of a `query% do` block. -/
declare_syntax_cat queryStmt

/-- Bind a table source: `let x ← from T`, where `T` has a `HasModel` instance. -/
syntax (name := queryBind) "let " ident " ← " "from " term : queryStmt
/-- A filter condition, e.g. `guard a.retired` or `guard b.author = a.name`. -/
syntax (name := queryGuard) "guard " term : queryStmt
/-- Project the query onto one of the bound variables: `select x`. -/
syntax (name := querySelect) "select " ident : queryStmt

/-- `query% do ...` elaborates a `do`-style query block into a `QuerySet`. -/
syntax (name := queryDo) "query%" "do" many1Indent(queryStmt) : term

/-- Information collected for each `let x ← from T` binder in a query block. -/
private structure QBinder where
  /-- The user-facing variable name (`x`). -/
  name : Name
  /-- The syntax of the binding identifier, used for error positions and info. -/
  ref : Syntax
  /-- The bound type `T`. -/
  type : Expr
  /-- The view of the table backing `T` (`Table.view idx : View db`). -/
  view : Expr
  /-- The table index `idx : db.Index`. -/
  idx : Expr
  /-- The database `T` lives in. -/
  db : Expr
  /-- The name of the column-index enum for `T` (e.g. `BookIndex`). -/
  indexType : Name
  deriving Inhabited

/-- The immutable context threaded through condition translation. -/
private structure Context where
  /-- The database all tables live in. -/
  db : Expr
  /-- The total view `V` of the joined tables; conditions are `DBExpr V _`. -/
  view : Expr
  /-- The expression `DBType.bool`, cached. -/
  boolTy : Expr
  /-- The binders, in join order. -/
  binders : Array QBinder
  /-- `injs[i] : (binders[i].view).Hom view` is the inclusion of table `i` into the total view. -/
  injs : Array Expr
  /-- Maps the free variable introduced for a binder to its position in `binders`/`injs`. -/
  fvarIdx : Std.HashMap FVarId Nat

/-- Reduce `e` to a head constant name, if it is (eventually) a constant application. -/
private def reduceToConstName (e : Expr) : MetaM (Option Name) := do
  let e ← whnf e
  if let some n := e.getAppFn.constName? then
    return some n
  let e ← reduce e
  return e.getAppFn.constName?

/-- Build the `DBExpr` for the column named `field` of the `bidx`-th bound table, together with
its `DBType`. -/
private def columnVar (ctx : Context) (bidx : Nat) (field : Name) : TermElabM (Expr × Expr) := do
  let b := ctx.binders[bidx]!
  let ctorName := b.indexType ++ field
  let indInfo ← getConstInfoInduct b.indexType
  unless indInfo.ctors.contains ctorName do
    let cols := String.intercalate ", " (indInfo.ctors.map (·.getString!))
    throwError m!"`{b.type}` has no column `{field}`; available columns: {cols}"
  let ctor := Lean.mkConst ctorName
  -- The actual `DBType` of the column, used to type the resulting expression.
  let t ← reduce (← mkAppM ``Column.type
    #[← mkAppM ``Database.Name.column #[← mkAppM ``View.name #[b.view, ctor]]])
  -- Inject the column index into the total view.
  let idx ← mkAppM ``View.Hom.map #[ctx.injs[bidx]!, ctor]
  -- `DBExpr.var` demands that `t` really is the type the view assigns to the column; `t` was
  -- computed from exactly that expression just above, so `rfl` proves it.
  let e ← mkAppOptM ``DBExpr.var
    #[some ctx.db, some ctx.view, some idx, some t, some (← mkEqRefl t)]
  return (e, t)

/-- The proof that a `DBType` is character data, for the concrete types the DSL produces. -/
private def mkTextLikeProof : TermElabM Expr :=
  mkEqRefl (Lean.mkConst ``Bool.true)

/-- Inside a `query% do` block, `like col pattern` is SQL's `col LIKE pattern`, where `%` and `_`
in `pattern` are wildcards. It has no meaning outside a query block. -/
def like {n : Nat} (_col : VarChar n) (_pattern : String) : Bool := false

/-- Inside a `query% do` block, `contains col s` matches the rows whose `col` contains `s` as a
substring, i.e. `col LIKE '%s%'` with the wildcards occurring in `s` escaped. It has no meaning
outside a query block. -/
def contains {n : Nat} (_col : VarChar n) (_s : String) : Bool := false

/-- Inside a `query% do` block, `isIn col [v₁, ..., vₙ]` is SQL's `col IN (v₁, ..., vₙ)`. It has no
meaning outside a query block. -/
def isIn {α : Type} (_col : α) (_values : List α) : Bool := false

mutual

/-- Translate an elaborated term into a `DBExpr ctx.db ctx.view t`, returning the pair `(expr, t)`.

The term was produced by elaborating a `guard`/`select` sub-expression against the local
variables standing for the bound tables, so column references appear as ordinary structure
projections (`Book.author b`), string literals as `VarChar.mk`, and the boolean connectives as
`Eq`/`And`/`Bool.and`. -/
private partial def transVal (ctx : Context) (e : Expr) : TermElabM (Expr × Expr) := do
  let args := e.getAppArgs
  -- Apply a `DBExpr` constructor; its database and view arguments are implicit and are
  -- determined by the sub-expressions.
  let mkE (ctor : Name) (as : Array Expr) : TermElabM Expr :=
    mkAppM ctor as
  -- A comparison of two values of the same type, yielding a boolean condition.
  let cmp (ctor : Name) (l r : Expr) : TermElabM (Expr × Expr) := do
    let (l, tl) ← transVal ctx l
    let (r, tr) ← transVal ctx r
    unless ← isDefEq tl tr do
      throwError m!"cannot compare a value of type `{← reduce tl}` with one of type `{← reduce tr}`"
    return (← mkE ctor #[l, r], ctx.boolTy)
  -- Equality of two values (also covers the `Bool → Prop` coercion `x = true`).
  if e.isAppOfArity ``Eq 3 then
    return ← cmp ``DBExpr.eq args[1]! args[2]!
  -- Disequality, either as `a ≠ b` or as `a != b`.
  if e.isAppOfArity ``Ne 3 then
    return ← cmp ``DBExpr.ne args[1]! args[2]!
  if e.isAppOfArity ``bne 4 then
    return ← cmp ``DBExpr.ne args[2]! args[3]!
  if e.isAppOfArity ``BEq.beq 4 then
    return ← cmp ``DBExpr.eq args[2]! args[3]!
  -- Ordering comparisons. `a > b` and `a ≥ b` are their own head constants in Lean, so both
  -- orientations have to be recognised.
  if e.isAppOfArity ``LT.lt 4 then
    return ← cmp ``DBExpr.lt args[2]! args[3]!
  if e.isAppOfArity ``LE.le 4 then
    return ← cmp ``DBExpr.le args[2]! args[3]!
  if e.isAppOfArity ``GT.gt 4 then
    return ← cmp ``DBExpr.gt args[2]! args[3]!
  if e.isAppOfArity ``GE.ge 4 then
    return ← cmp ``DBExpr.ge args[2]! args[3]!
  -- Conjunction, either as a proposition (`∧`) or on booleans (`&&`).
  if e.isAppOfArity ``And 2 then
    return (← mkE ``DBExpr.and #[← transBool ctx args[0]!, ← transBool ctx args[1]!], ctx.boolTy)
  if e.isAppOfArity ``Bool.and 2 then
    return (← mkE ``DBExpr.and #[← transBool ctx args[0]!, ← transBool ctx args[1]!], ctx.boolTy)
  -- Disjunction, either as a proposition (`∨`) or on booleans (`||`).
  if e.isAppOfArity ``Or 2 then
    return (← mkE ``DBExpr.or #[← transBool ctx args[0]!, ← transBool ctx args[1]!], ctx.boolTy)
  if e.isAppOfArity ``Bool.or 2 then
    return (← mkE ``DBExpr.or #[← transBool ctx args[0]!, ← transBool ctx args[1]!], ctx.boolTy)
  -- Negation, either as a proposition (`¬`) or on booleans (`!`).
  if e.isAppOfArity ``Not 1 then
    return (← mkE ``DBExpr.not #[← transBool ctx args[0]!], ctx.boolTy)
  if e.isAppOfArity ``Bool.not 1 then
    return (← mkE ``DBExpr.not #[← transBool ctx args[0]!], ctx.boolTy)
  -- Null tests, written on the `Option`-valued field of a nullable column.
  if e.isAppOfArity ``Option.isNone 2 then
    return (← mkE ``DBExpr.isNull #[(← transVal ctx args[1]!).1], ctx.boolTy)
  if e.isAppOfArity ``Option.isSome 2 then
    return (← mkE ``DBExpr.isNotNull #[(← transVal ctx args[1]!).1], ctx.boolTy)
  -- `LIKE`, `LIKE '%s%'` and `IN (...)`, which have no Lean surface syntax of their own and are
  -- written with the marker functions of this module.
  if e.isAppOfArity ``Db.Query.DSL.like 3 then
    let (l, tl) ← transVal ctx args[1]!
    return (← mkAppOptM ``DBExpr.like
      #[some ctx.db, some ctx.view, some tl, some l, some args[2]!, some (← mkTextLikeProof)],
      ctx.boolTy)
  if e.isAppOfArity ``Db.Query.DSL.contains 3 then
    let (l, tl) ← transVal ctx args[1]!
    return (← mkAppOptM ``DBExpr.contains
      #[some ctx.db, some ctx.view, some tl, some l, some args[2]!, some (← mkTextLikeProof)],
      ctx.boolTy)
  if e.isAppOfArity ``Db.Query.DSL.isIn 3 then
    let (l, tl) ← transVal ctx args[1]!
    return (← mkAppOptM ``DBExpr.inList
      #[some ctx.db, some ctx.view, some tl, some l, some args[2]!], ctx.boolTy)
  -- A nullable column projects to an `Option`-valued field, so a comparison against a literal is
  -- written `col = some v`. `DBExpr` does not track nullability, so `some` is simply dropped. There
  -- is deliberately no case for `none`: `col = NULL` is never true in SQL, `col.isNone` is meant.
  if e.isAppOfArity ``Option.some 2 then
    return ← transVal ctx args[1]!
  if e.isConstOf ``True || e.isConstOf ``Bool.true then
    return (← mkAppOptM ``DBExpr.true #[some ctx.db, some ctx.view], ctx.boolTy)
  if e.isConstOf ``False || e.isConstOf ``Bool.false then
    return (← mkAppOptM ``DBExpr.false #[some ctx.db, some ctx.view], ctx.boolTy)
  -- A column reference: a structure projection `T.field x` applied to a bound variable `x`.
  if e.getAppFn.isConst && !args.isEmpty && args.back!.isFVar then
    if let some bidx := ctx.fvarIdx.get? args.back!.fvarId! then
      return ← columnVar ctx bidx (Name.mkSimple e.getAppFn.constName!.getString!)
  -- Anything else that has the type of a database value is a constant of the query: it is
  -- evaluated when the query is built and embedded as a literal.
  let ty ← whnf (← inferType e)
  if ty.isAppOfArity ``VarChar 1 then
    let n := ty.appArg!
    let t := mkApp (mkConst ``DBType.varchar) n
    return (← mkAppOptM ``DBExpr.str #[some ctx.db, some ctx.view, some n, some e], t)
  if ty.isConstOf ``Int then
    return (← mkAppOptM ``DBExpr.int #[some ctx.db, some ctx.view, some e],
      Lean.mkConst ``DBType.int)
  throwError m!"unsupported expression in query condition: `{e}`"

/-- Translate a term that is expected to denote a boolean condition. -/
private partial def transBool (ctx : Context) (e : Expr) : TermElabM Expr := do
  let (de, t) ← transVal ctx e
  unless ← isDefEq t ctx.boolTy do
    throwError m!"expected a boolean condition, but got a value of type `{← reduce t}`"
  return de

end

/-- Introduce a fresh local variable `x : T` for each binder and run `k` with them in scope. -/
private partial def withBinderFVars {α} (binders : Array QBinder) (i : Nat) (fvars : Array Expr)
    (k : Array Expr → TermElabM α) : TermElabM α :=
  if h : i < binders.size then
    withLocalDeclD binders[i].name binders[i].type fun fv =>
      withBinderFVars binders (i + 1) (fvars.push fv) k
  else
    k fvars

@[term_elab queryDo]
def elabQueryDo : TermElab := fun stx expectedType? => do
  let `(query% do $stmts*) := stx
    | throwUnsupportedSyntax
  -- Partition the statements by kind.
  let mut binderStx : Array (Ident × Term) := #[]
  let mut guardStx : Array Term := #[]
  let mut selectStx? : Option Ident := none
  for stmt in stmts do
    match stmt with
    | `(queryStmt| let $x:ident ← from $t:term) =>
        binderStx := binderStx.push (x, t)
    | `(queryStmt| guard $c:term) =>
        if selectStx?.isSome then
          throwErrorAt stmt "`guard` must come before `select`"
        guardStx := guardStx.push c
    | `(queryStmt| select $x:ident) =>
        if selectStx?.isSome then
          throwErrorAt stmt "a query may contain at most one `select`"
        selectStx? := some x
    | _ => throwErrorAt stmt "unexpected query statement"
  let some selectIdent := selectStx?
    | throwError "query is missing a `select` clause"
  if binderStx.isEmpty then
    throwError "query must bind at least one table with `let x ← from T`"
  -- Elaborate each binder into a `QBinder`.
  let mut binders : Array QBinder := #[]
  for (x, tStx) in binderStx do
    let T ← Term.elabType tStx
    if (← optional (synthInstance (← mkAppM ``HasModel #[T]))).isNone then
      throwErrorAt tStx
        m!"`{T}` cannot be used as a query source: no `HasModel {T}` instance found"
    -- Elaborated from `tStx` since `HasModel.database`/`HasModel.model` rebind their type
    -- argument explicitly and don't compose well with `mkAppM`.
    let db ← instantiateMVars (← Term.elabTerm (← `(HasModel.database $tStx)) none)
    let idx ← instantiateMVars (← Term.elabTerm (← `((HasModel.model $tStx).index)) none)
    let view ← mkAppM ``Table.view #[idx]
    let some indexType ← reduceToConstName (← mkAppM ``View.Index #[view])
      | throwErrorAt tStx m!"could not determine the columns of `{T}`"
    binders := binders.push
      { name := x.getId, ref := x, type := T, view := view, idx := idx
        db := db, indexType := indexType }
  -- All tables must live in the same database.
  let db₀ := binders[0]!.db
  for b in binders do
    unless ← isDefEq db₀ b.db do
      throwErrorAt b.ref
        m!"table `{b.type}` belongs to a different database than `{binders[0]!.type}`"
  -- Build the cross join of all tables, the total view `V`, and the inclusion `View.Hom`s of each
  -- table's view into `V`.
  let mut qAcc ← mkAppOptM ``Query.all #[some db₀, some binders[0]!.idx]
  let mut viewAcc := binders[0]!.view
  let mut injAcc : Array Expr := #[← mkAppM ``View.Hom.id #[binders[0]!.view]]
  for h : i in [1:binders.size] do
    let b := binders[i]
    let inl ← mkAppM ``View.sumInl #[viewAcc, b.view]
    injAcc ← injAcc.mapM fun inj => mkAppM ``View.Hom.comp #[inj, inl]
    injAcc := injAcc.push (← mkAppM ``View.sumInr #[viewAcc, b.view])
    qAcc ← mkAppM ``Query.join #[qAcc, ← mkAppOptM ``Query.all #[some db₀, some b.idx]]
    viewAcc ← mkAppM ``View.prod #[viewAcc, b.view]
  let qJoin := qAcc
  let totalView := viewAcc
  let injs := injAcc
  -- Reject duplicate variable names up front for a clearer error than shadowing.
  let mut nameSet : Std.HashSet Name := {}
  for b in binders do
    if nameSet.contains b.name then
      throwErrorAt b.ref m!"duplicate query variable `{b.name}`"
    nameSet := nameSet.insert b.name
  -- Introduce a real local variable `x : T` for each binder, then elaborate the `guard`/`select`
  -- clauses as ordinary terms in that context so the editor sees genuine locals.
  withBinderFVars binders 0 #[] fun fvars => do
    let mut fvarIdx : Std.HashMap FVarId Nat := {}
    for h : i in [0:binders.size] do
      Term.addLocalVarInfo binders[i].ref fvars[i]!
      fvarIdx := fvarIdx.insert fvars[i]!.fvarId! i
    let ctx : Context :=
      { db := db₀, view := totalView, boolTy := Lean.mkConst ``DBType.bool
        binders := binders, injs := injs, fvarIdx := fvarIdx }
    -- Apply the guards as filters.
    let mut q := qJoin
    for g in guardStx do
      let e ← instantiateMVars (← Term.elabTerm g none)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      q ← mkAppM ``Query.filter #[← transBool ctx e, q]
    -- Project onto the selected variable and wrap the result in a `QuerySet`.
    let selE ← instantiateMVars (← Term.elabTerm selectIdent none)
    let some bidx := selE.fvarId?.bind fvarIdx.get?
      | throwErrorAt selectIdent m!"`select` must name one of the bound query variables"
    let projQ ← mkAppM ``Query.project #[injs[bidx]!, q]
    let qs ← mkAppOptM ``QuerySet.mk #[some binders[bidx]!.type, none, some projQ]
    -- Register a term info spanning the whole block body, carrying the local context with the
    -- bound variables in scope. `hoverableInfoAt?` only matches nodes whose (canonical) range
    -- contains the cursor, so without this the info view shows nothing when the cursor sits in the
    -- "gaps" between sub-terms (line starts, the `guard`/`select` keywords, blank lines). This node
    -- is larger than every sub-term but smaller than the enclosing block, so it fills exactly those
    -- gaps while precise hovers still win on the terms themselves.
    if let (some p0, some pN) := (stmts[0]!.raw.getPos?, stmts[stmts.size - 1]!.raw.getTailPos?) then
      let text ← getFileMap
      let lineStart := text.ofPosition { line := (text.toPosition p0).line, column := 0 }
      Term.addTermInfo'
        (Syntax.atom (.original "".toRawSubstring lineStart "".toRawSubstring pN) "") qs
    match expectedType? with
    | some expected => ensureHasType expected qs
    | none => return qs

end Db.Query.DSL
