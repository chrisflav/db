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

The two guards do different jobs. This module keeps libpq out of what `import Db` drags in; the
option keeps the FFI shim out of the *build*, which the import cannot do, since Lake compiles and
links a package's external libraries into every executable built from it regardless of which modules
that executable imports.

Importing this module works either way: without the option the declarations below are elaborated
from `.olean`s with nothing behind their `@[extern]` attributes, which is all type-checking needs.
It is linking an executable that calls them that needs `postgres = "on"` — and, because Lake does
not propagate link arguments to dependents, libpq in that executable's own `moreLinkArgs`. The
README has the snippet.
-/
