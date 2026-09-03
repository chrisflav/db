import Lake

open System Lake DSL

/-- Ask `pg_config` for a directory; `none` if it is not installed or fails. -/
def pgConfig (flag : String) : IO (Option FilePath) := do
  try
    let out ← IO.Process.output { cmd := "pg_config", args := #[flag] }
    let dir : String := out.stdout.trim
    if out.exitCode == 0 && !dir.isEmpty then
      return some (FilePath.mk dir)
    return none
  catch _ =>
    return none

/-- The libpq shared library, by absolute path: Lean's bundled `lld` does not search the system
library directories, and pointing it there with `-L` also picks up the system's glibc CRT objects,
which do not match the toolchain's. So the path comes from `pg_config --libdir`, falling back to
the Debian location. -/
def libpqPath : IO FilePath := do
  let fallback : FilePath := "/usr/lib/x86_64-linux-gnu/libpq.so"
  let some libdir ← pgConfig "--libdir" | return fallback
  for name in ["libpq.so", "libpq.dylib"] do
    let candidate := libdir / name
    if ← candidate.pathExists then
      return candidate
  return fallback

/-- The directory holding `libpq-fe.h`, from `pg_config --includedir`. -/
def libpqIncludeDir : IO FilePath := do
  return (← pgConfig "--includedir").getD "/usr/include/postgresql"

-- Evaluated when Lake loads the configuration, once per build.
unsafe def linkArgsImpl : Array String :=
  unsafeBaseIO do
    match ← libpqPath.toBaseIO with
    | .ok path => return #[path.toString]
    | .error _ => return #["/usr/lib/x86_64-linux-gnu/libpq.so"]

/-- The link arguments for libpq; the fallback is only for the checker, `linkArgsImpl` is what
runs. -/
@[implemented_by linkArgsImpl]
def linkArgs : Array String :=
  #["/usr/lib/x86_64-linux-gnu/libpq.so"]

package db where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLinkArgs := linkArgs

input_file ffi_postgresql_basic.cpp where
  path := "c" / "postgresql" / "basic.cpp"
  text := true

target ffi_postgresql.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi_static.o"
  let srcJob ← ffi_postgresql_basic.cpp.fetch
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", (← libpqIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

extern_lib libleanffi_postgresql pkg := do
  let ffiO ← ffi_postgresql.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib Db

lean_lib Db.Backends.PostgreSQL.FFI where
  precompileModules := true
  moreLinkObjs := #[libleanffi_postgresql]

lean_lib Db.Examples

@[test_driver] lean_exe testdb where
  root := `Db.Examples.Main

require quot4 from git "https://github.com/leanprover-community/quote4" @ "v4.31.0"

require leansqlite from git
  "https://github.com/leanprover/leansqlite" @ "b61f1cfac14d03094cb3c0e65acd504416e47cad"

@[default_target] lean_exe db where
  root := `Main
