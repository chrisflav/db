import Db.Query.Basic

structure Interpretation (query : Type) where
  fromQuery {d : Database} (names : Std.HashSet d.Name) (q : Query d names) : query

/-- An interpretation monad on the database `d` provides lookup and modification operations. -/
class DBMonad (d : Database) (m : Type → Type) where
  /-- Lookup the given query on the database. -/
  lookup {names : Std.HashSet d.Name} (q : Query d names) :
    m (Std.DHashMap d.Name (fun d ↦ d.dbtype.Value))
