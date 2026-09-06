import Db.Examples

/-- The self-contained half of the example suite: the SQLite backend against a temporary database,
    needing no server and no libpq. This is what `lake test` runs.

    The PostgreSQL examples are `lake exe testdb-postgres`. -/
def main : IO Unit := do
  SqliteExample.test
