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

    Falls back to `-lpq` when `pg_config` is absent, which is right where libpq sits somewhere the
    linker already searches. -/
def libpqLinkArgs : IO (Array String) := do
  let some dir ← toolOutput? "pg_config" #["--libdir"] | return #["-lpq"]
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

extern_lib libleanffi_postgresql pkg := do
  let ffiO ← ffi_postgresql.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

/-- The library proper: the query language, the model layer, the migrations and the SQLite backend.

    `Db.Postgres` is deliberately not reachable from the `Db` root module, so that a package
    depending on this one does not build the FFI shim (which needs the PostgreSQL headers) or link
    libpq unless it asks for the backend. -/
lean_lib Db

lean_lib Db.Backends.PostgreSQL.FFI where
  precompileModules := true
  moreLinkObjs := #[libleanffi_postgresql]

/-- The PostgreSQL backend, and the `Db.Postgres` module that is its entry point. -/
lean_lib Db.Postgres where
  needs := #[libleanffi_postgresql]

lean_lib Db.Examples

/-- The SQLite half of the example suite. Self-contained: it needs no server and no libpq, so it is
    the test driver and runs anywhere. -/
@[test_driver] lean_exe testdb where
  root := `Db.Examples.Main

/-- The PostgreSQL half. Needs a server to talk to and libpq to link against, so it is a target of
    its own rather than part of `lake test`. -/
lean_exe «testdb-postgres» where
  root := `Db.Examples.PostgresMain
  moreLinkArgs := run_io libpqLinkArgs

require quot4 from git "https://github.com/leanprover-community/quote4" @ "v4.31.0"

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "b61f1cfac14d03094cb3c0e65acd504416e47cad"

@[default_target] lean_exe db where
  root := `Main
