/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db
import Db.Backends.PostgreSQL.Basic

def main : IO Unit := do
  let conn ← PostgreSQL.connect "postgresql://testuser:secret@localhost/testdb2"
  match conn with
  | some conn =>
    let res ← conn.exec "SELECT * FROM fish"
    match res with
    | .data data =>
      IO.println s!"Table OID of col 0: {data.raw.ftable 0}"
      IO.println s!"Returned {data.nrows} rows with {data.ncolumns} columns."
      let columns := data.columns
      IO.println s!"Lengths: {columns["length"]!}"
    | _ => IO.println "Unexpected response."
  | none =>
    IO.println "Connection failed."
