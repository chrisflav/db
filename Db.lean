import Db.Backends.Sql
import Db.Backends.SQLite.Interpretation
import Db.Interpretation.Basic
import Db.Query.Basic
import Db.Query.DSL
import Db.Utils.VarChar
import Db.Migration.Basic
import Db.Migration.Recipe
import Db.Model

/-!
# Db

The query language, the model layer, the migration framework and the SQLite backend.

The PostgreSQL backend is deliberately *not* imported here. It is an FFI binding against libpq,
and importing it from the root module made every package that depends on this one link libpq and
need the PostgreSQL headers to build, whether or not it ever opened a PostgreSQL connection.
`import Db.Postgres` to get it.

The import boundary alone does not go far enough, because Lake builds and links the external
libraries of every package owning an imported module into every executable. The FFI shim is
therefore also behind the `postgres` Lake configuration option, off by default, so that a package
importing only this module builds with nothing but a C compiler present — no PostgreSQL headers, no
libpq. See the README for the configuration a PostgreSQL user adds.
-/
