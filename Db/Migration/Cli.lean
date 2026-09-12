/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db.Migration.Generate

/-!
# The migration command line

A project that uses declarative migrations wants the four commands Django has: apply the pending
migrations, list what is applied, write the migration that closes the gap, and — for CI — fail if
there is a gap. They are the same four commands for every project; what differs is the migration
list, the declared schema, where the files go and how a database action is run.

So this is a `main` a project supplies those four things to, rather than an executable of its own:
the backend and the connection are the project's business, and the library has no business opening
a connection out of a configuration file it invented.
-/

namespace Db.Migration.Cli

/-- What a project has to supply to get the four commands. -/
structure Config (m : Type → Type) : Type 1 where
  /-- Every migration the project declares, oldest first. This is the list that is committed; the
  database is compared against it. -/
  migrations : List Migration
  /-- The schema the code declares, typically `(%database mydb).recipe`, possibly
  `.withIndexes …`. -/
  target : DatabaseRecipe
  /-- Where `makemigrations` writes files. -/
  directory : System.FilePath
  /-- Run a database action; the backend and the connection are the project's business. -/
  run : {α : Type} → m α → IO α

/-- What the commands are. -/
def usage : String :=
  "usage: <command>\n" ++
  "  migrate                      apply every migration the database has not recorded\n" ++
  "  showmigrations               list the migrations, marking the applied ones\n" ++
  "  makemigrations <description> write the migration closing the gap to the declared schema\n" ++
  "  check                        exit 1 if a migration would have to be written (for CI)"

variable {m : Type → Type} [Monad m] [DBMonadWithMigrations m] [DBMonadTransactional m]

/-- Apply the pending migrations, recording the current time against each. -/
def migrateCommand (cfg : Config m) : IO UInt32 := do
  -- The clock is read here rather than in `migrate`: that one takes the time as an argument so
  -- that it stays reproducible in a test and does not force its monad to be over `IO`.
  let now := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val
  let applied ← cfg.run (Db.Migration.migrate cfg.migrations now)
  if applied.isEmpty then
    IO.println "Nothing to migrate."
  else
    for name in applied do
      IO.println s!"Applied {name}."
  return 0

/-- List every declared migration, marking the ones the database records. -/
def showCommand (cfg : Config m) : IO UInt32 := do
  let done ← cfg.run (Db.Migration.applied (m := m))
  for mig in cfg.migrations do
    IO.println s!"[{if done.contains mig.name then "X" else " "}] {mig.name}"
  -- A migration the database records and the code does not declare is the state `migrate` refuses
  -- to run in, so it is worth seeing here rather than only at the point of failure.
  for name in done do
    unless cfg.migrations.any (·.name == name) do
      IO.println s!"[X] {name} (recorded, but not declared by this code)"
  return 0

/-- Write the migration that closes the gap between the declared schema and the migrations. -/
def makeCommand (cfg : Config m) (description : String) : IO UInt32 := do
  match planSteps cfg.migrations cfg.target with
  | .error e =>
    IO.eprintln s!"Cannot write a migration: {e}"
    return 1
  | .ok [] =>
    IO.println "No changes detected."
    return 0
  | .ok steps =>
    -- The description is sanitised into the name, not only into the identifier `render` derives
    -- from it: the name is also the file name, and a Lean module whose path has a space in it
    -- cannot be imported.
    let name := s!"{nextNumber cfg.migrations}_{identifierOfName description}"
    let path := cfg.directory / s!"{name}.lean"
    IO.FS.createDirAll cfg.directory
    IO.FS.writeFile path (render name steps)
    IO.println s!"Wrote {path}."
    IO.println s!"Add `migration_{identifierOfName name}` to the migration list to apply it."
    return 0

/-- Report whether a migration would have to be written, for CI. -/
def checkCommand (cfg : Config m) : IO UInt32 := do
  match planSteps cfg.migrations cfg.target with
  | .error e =>
    IO.eprintln s!"Cannot write a migration: {e}"
    return 1
  | .ok [] =>
    IO.println "No changes detected."
    return 0
  | .ok steps =>
    IO.eprintln "The declared schema is ahead of the migrations. Missing steps:"
    for step in steps do
      IO.eprintln s!"  {step.describe}"
    return 1

/-- The migration command line: dispatch `args` over the four commands. Returns the exit code, so
that a project's `main` can do something else afterwards. -/
def main (cfg : Config m) (args : List String) : IO UInt32 := do
  match args with
  | ["migrate"] => migrateCommand cfg
  | ["showmigrations"] => showCommand cfg
  | ["makemigrations", description] => makeCommand cfg description
  | ["check"] => checkCommand cfg
  | _ =>
    IO.eprintln usage
    return 2

end Db.Migration.Cli
