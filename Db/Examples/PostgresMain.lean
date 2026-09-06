import Db.Examples.Postgres

/-- The PostgreSQL half of the example suite. Needs a server at the connection string the examples
    name, so it is run on demand rather than by `lake test`. -/
def main : IO Unit := do
  BookExample.test
