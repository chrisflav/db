import Lake

open System Lake DSL

def linkArgs :=
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
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", "/usr/include/postgresql"]
  buildO oFile srcJob weakArgs #["-fPIC"] "c++" getLeanTrace

extern_lib libleanffi_postgresql pkg := do
  let ffiO ← ffi_postgresql.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib Db

lean_lib Db.Backends.PostgreSQL.FFI where
  precompileModules := true
  moreLinkObjs := #[libleanffi_postgresql]

require quot4 from git "https://github.com/leanprover-community/quote4" @ "v4.27.0-rc1"

@[default_target] lean_exe db where root := `Main
