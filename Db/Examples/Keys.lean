/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Examples.Schema

/-!
# The declared-primary-key demo

One demo, run on both backends, for a model whose key is a field of its own rather than an id the
database assigns — and for `HasModel.save`, which is what such a model is written with: an insert
that replaces the row already under the key.

Shared rather than written twice because the statements are the same on both, and because
PostgreSQL is the stricter of the two about `ON CONFLICT`: it insists on a conflict target for a
`DO UPDATE`, and the target has to be a key it actually has.
-/

namespace KeyExample

open BookExample HasModel DBMonadWithMigrations Db.Query.DSL

variable {m : Type → Type} [Monad m] [DBMonadWithMigrations m] [MonadLiftT IO m]

/-- Exercise a declared key end to end: the key reaches `CREATE TABLE`, a second insert of the same
key conflicts on it rather than storing a duplicate, and `save` replaces the row that is there. -/
def keyDemo (label : String) : m Unit := do
  autoUpdate (%database mydb)
  -- The PostgreSQL database is shared between the demos and keeps what the last run left.
  let _ ← HasModel.delete (α := Profile) .true
  let _ ← HasModel.delete (α := Event) .true
  let _ ← HasModel.delete (α := Membership) .true
  IO.println s!"Declared primary keys ({label}):"
  -- The key as the generated table declares it, in the order it was named in.
  IO.println <|
    s!"  profile: {(HasModel.model Profile).table.primaryKey.map toString}, " ++
    s!"event: {(HasModel.model Event).table.primaryKey.map toString}"
  -- A second row under the same key is a conflict, which is what the key is for.
  let first ← HasModel.insertIfAbsent
    ({ handle := "ada", displayName := "Ada", visits := 1 } : Profile)
  let again ← HasModel.insertIfAbsent
    ({ handle := "ada", displayName := "Someone else", visits := 9 } : Profile)
  IO.println s!"  insertIfAbsent, then the same handle again: {first}, {again}"
  -- `save` replaces the row under the key: one row, with the new values.
  HasModel.save ({ handle := "ada", displayName := "Ada Lovelace", visits := 42 } : Profile)
  HasModel.save ({ handle := "grace", displayName := "Grace Hopper", visits := 7 } : Profile)
  HasModel.save ({ handle := "ada", displayName := "A. Lovelace", visits := 43 } : Profile)
  let profiles ← fetch ((QuerySet.all (α := Profile)).orderBy [{ column := ProfileIndex.handle }])
  IO.println s!"  after three saves, {profiles.size} profile(s):"
  for p in profiles do
    IO.println s!"    {p.handle}: {p.displayName}, {p.visits} visit(s)"
  -- A composite key conflicts only when both of its columns match.
  HasModel.save ({ session := "s1", seq := 1, body := "hello" } : Event)
  HasModel.save ({ session := "s1", seq := 2, body := "world" } : Event)
  HasModel.save ({ session := "s2", seq := 1, body := "elsewhere" } : Event)
  HasModel.save ({ session := "s1", seq := 2, body := "rewritten" } : Event)
  let events ← fetch ((QuerySet.all (α := Event)).orderBy
    [{ column := EventIndex.session }, { column := EventIndex.seq }])
  IO.println s!"  after four saves, {events.size} event(s):"
  for e in events do
    IO.println s!"    {e.session}/{e.seq}: {e.body}"
  -- Every column is in the key here, so `save` has nothing to set and leaves the row alone.
  HasModel.save ({ groupName := "admins", member := "ada" } : Membership)
  HasModel.save ({ groupName := "admins", member := "ada" } : Membership)
  IO.println s!"  memberships after saving the same one twice: {← HasModel.count (QuerySet.all (α := Membership))}"
  -- The key reaches the database and comes back: `autoUpdate` reports no constraint mismatch for
  -- these tables, which is what it does for a declared key the database does not have.
  autoUpdate (%database mydb)
  let current ← currentDatabase
  IO.println <|
    s!"  keys read back — profile: {(current.tables["profile"]?.map (·.primaryKey)).getD []}, " ++
    s!"event: {(current.tables["event"]?.map (·.primaryKey)).getD []}"
  IO.println <|
    s!"  pending operations after two autoUpdates: " ++
    s!"{(current.operations (%database mydb).recipe).size}, constraint mismatches: " ++
    s!"{current.constraintMismatches (%database mydb).recipe}"
  -- The rows are this demo's to clean up, for the next run against a server that keeps them.
  let _ ← HasModel.delete (α := Profile) .true
  let _ ← HasModel.delete (α := Event) .true
  let _ ← HasModel.delete (α := Membership) .true

end KeyExample
