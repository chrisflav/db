/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-!
# The SQL dialect a backend speaks

A module of its own, holding nothing but the `SQL.Dialect` enumeration.

It used to live in `Db.Backends.Sql`, where the statements that depend on it are rendered. It
cannot stay there now that `DBMonadWithMigrations` reports the dialect its backend speaks: that
class is in `Db.Interpretation.Basic`, which `Db.Backends.Sql` imports, so naming `Dialect` from
the class would close a cycle. The alternative — a `String` on the class, parsed back where a
statement is rendered — would turn a closed two-case match into a partial one, so the enumeration
moved instead.
-/

namespace SQL

/-- The SQL dialect a statement is rendered in. The two backends disagree on two things only: how
an auto-incrementing primary key is declared, and whether an `ON CONFLICT` may follow a
`DEFAULT VALUES`. Nothing else in the rendering depends on the dialect — quoted identifiers are
spelled the same way by both. -/
inductive Dialect where
  | postgres
  | sqlite
  deriving Repr, BEq, DecidableEq

end SQL
