import Db.Examples

def main : IO Unit := do
  -- Self-contained demo using the SQLite backend (no external server required).
  SqliteExample.test
  -- Demo using the PostgreSQL backend (requires a running PostgreSQL server).
  BookExample.test
  -- Tests of the PostgreSQL bindings; skipped unless `DB_TEST_URL` names a server.
  PostgresTests.test
