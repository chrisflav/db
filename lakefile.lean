import Lake

open System Lake DSL

/-- Run `cmd args` and return its trimmed standard output, or `none` if it is not installed or
    fails. -/
def toolOutput? (cmd : String) (args : Array String) : IO (Option String) := do
  let out ← IO.Process.output { cmd, args }
    |>.catchExceptions fun _ => pure { exitCode := 1, stdout := "", stderr := "" }
  let text := out.stdout.trimAscii.toString
  if out.exitCode == 0 && !text.isEmpty then return some text else return none

/-- Split a tool's output into whitespace-separated arguments. -/
def splitArgs (s : String) : Array String :=
  s.split Char.isWhitespace |>.map (·.toString) |>.filter (!·.isEmpty) |>.toArray

/-- The linker arguments the PostgreSQL FFI shim needs: the absolute path of the libpq shared
    library, discovered through `pg_config`.

    Named as a path rather than as `-L<dir> -lpq` for the reason the hardcoded path here originally
    was: the toolchain ships its own `clang` and C runtime, and putting the system library directory
    on its search path makes it resolve glibc there too, which fails to link against the toolchain's
    `Scrt1.o`. Passing the one library by path takes libpq without the directory around it.

    `pkg-config` is asked first and `pg_config` second, because the two are packaged apart on some
    distributions: nixpkgs' libpq ships the `.pc` file and no `pg_config` at all — that belongs to
    the server package, which a machine building a client has no reason to install — so asking
    only `pg_config` finds nothing there, falls through to `-lpq`, and then fails to link for the
    reason above. `libpqIncludeArgs` below already prefers `pkg-config`; this is the same order.

    Falls back to `-lpq` when neither tool knows, which is right where libpq sits somewhere the
    linker already searches. -/
def libpqLinkArgs : IO (Array String) := do
  let dirs := (← toolOutput? "pkg-config" #["--variable=libdir", "libpq"]).toArray
    ++ (← toolOutput? "pg_config" #["--libdir"]).toArray
  for dir in dirs do
    for ext in ["so", "dylib", "a"] do
      let candidate : FilePath := FilePath.mk dir / s!"libpq.{ext}"
      if ← candidate.pathExists then
        return #[candidate.toString]
  return #["-lpq"]

/-- The include directory holding `libpq-fe.h`. -/
def libpqIncludeArgs : IO (Array String) := do
  match (← toolOutput? "pkg-config" #["--cflags", "libpq"]).map splitArgs with
  | some args => return args
  | none =>
    let dir := (← toolOutput? "pg_config" #["--includedir"]).getD "/usr/include/postgresql"
    return #["-I", dir]

package db where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- No `moreLinkArgs` here on purpose. Link arguments set on the package are not propagated to a
  -- package that depends on this one, but the `extern_lib` below *is* — so a dependent that pulled
  -- in the PostgreSQL FFI got the shim's object file without the libpq it calls into, and failed to
  -- link with undefined `PQ*` symbols. The libpq arguments belong to the targets that use the shim.

input_file ffi_postgresql_basic.cpp where
  path := "c" / "postgresql" / "basic.cpp"
  text := true

target ffi_postgresql.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi_static.o"
  let srcJob ← ffi_postgresql_basic.cpp.fetch
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← libpqIncludeArgs)
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

/-- Whether to build the PostgreSQL backend's FFI shim and link libpq. Off by default.

    Hiding the backend behind `import Db.Postgres` was not enough on its own: Lake links the
    `extern_lib`s of every package that owns an imported module into every executable built from it,
    and builds them first. So the shim below was compiled — needing a C++ compiler and
    `libpq-fe.h` — for a package that only ever uses SQLite and never mentions `Db.Postgres`. A
    target that must not be built has to be absent from the configuration, and a Lake option is the
    only thing that can remove one; an import boundary cannot.

    Turn it on with `lake build -Kpostgres=on` in this repository, or, from a dependent, with
    `options = {postgres = "on"}` in its `[[require]]` (`lakefile.lean`:
    ``require db from git "…" with NameMap.empty.insert `postgres "on"``).

    Any value but an explicit negative counts as on, so that `-Kpostgres` and `-Kpostgres=1` mean
    what they look like, while someone turning the backend back off with `postgres = "off"` is not
    surprised by it staying on. -/
def postgresEnabled : Bool :=
  match get_config? postgres with
  | none => false
  | some value => !(["off", "false", "no", "0"].contains value.toLower)

meta if postgresEnabled then
extern_lib libleanffi_postgresql pkg := do
  let ffiO ← ffi_postgresql.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

/-- The library proper: the query language, the model layer, the migrations and the SQLite backend.

    `Db.Postgres` is deliberately not reachable from the `Db` root module, so that a package
    depending on this one does not build the FFI shim (which needs the PostgreSQL headers) or link
    libpq unless it asks for the backend.

    Its root also claims every `Db.*` module that no later library claims, and that is what keeps
    the PostgreSQL modules type-checking when `postgres` is off: they are then built as ordinary
    `.olean`s, with nothing behind their `@[extern]` declarations. Elaborating `import Db.Postgres`
    needs no more than that. Only an executable that actually calls into libpq needs the shim, and
    that is exactly what the option guards. -/
lean_lib Db

-- A `meta if` must not be preceded by a doc comment: Lean reads `meta` as the declaration modifier
-- it also is and then rejects the `if`. The doc comments therefore sit inside the guarded command.
meta if postgresEnabled then
/-- The Lean side of the FFI shim. It is precompiled and carries the object file, so it exists only
    when the option is on; otherwise `lean_lib Db` builds the same modules without either. -/
lean_lib Db.Backends.PostgreSQL.FFI where
  precompileModules := true
  moreLinkObjs := #[libleanffi_postgresql]

meta if postgresEnabled then
/-- The PostgreSQL backend, and the `Db.Postgres` module that is its entry point. Declared only
    when the option is on, since `needs` is what pulls the shim into a dependent's link. -/
lean_lib Db.Postgres where
  needs := #[libleanffi_postgresql]

lean_lib Db.Examples

/-- The SQLite half of the example suite. Self-contained: it needs no server and no libpq, so it is
    the test driver and runs anywhere. -/
@[test_driver] lean_exe testdb where
  root := `Db.Examples.Main

meta if postgresEnabled then
/-- The PostgreSQL half. Needs a server to talk to and libpq to link against, so it is a target of
    its own rather than part of `lake test`, and it exists only under `-Kpostgres=on` — for
    `lake exe` as much as for `lake build`, since both resolve the target out of the same
    configuration. -/
lean_exe «testdb-postgres» where
  root := `Db.Examples.PostgresMain
  moreLinkArgs := run_io libpqLinkArgs

require quot4 from git "https://github.com/leanprover-community/quote4" @ "v4.31.0"

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "0be4df908d1a8e75b58961041e2b4973692623df"

@[default_target] lean_exe db where
  root := `Main
