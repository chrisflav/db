/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db
import Db.Backends.PostgreSQL.Interpretation

/-!
# The PostgreSQL backend

`Db` itself is backend-neutral apart from SQLite, whose driver is vendored by `leansqlite` and so
costs a dependent package nothing. PostgreSQL is an FFI binding against libpq, which a package that
never opens a PostgreSQL connection should not have to have installed, so it lives behind this
module and behind the `postgres` Lake configuration option.
-/
