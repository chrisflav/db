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
`import Db.Postgres` to get it, and see the README for the Lake configuration that goes with it.
-/
