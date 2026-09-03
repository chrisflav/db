/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Db

/-!
# PostgreSQL backend tests

These exercise the raw bindings — parameterised statements, error reporting, notifications, the
connection lifecycle and memory behaviour — against a real server. They run only when
`DB_TEST_URL` names one (an ordinary user is enough: everything happens in temporary tables) and
are skipped otherwise.
-/

namespace PostgresTests

open PostgreSQL

/-- Fail the test run with `message` unless `cond` holds. -/
def check (cond : Bool) (message : String) : IO Unit := do
  unless cond do
    throw (IO.userError s!"check failed: {message}")

/-- Run `x` and return the `SqlError` it raised, failing if it succeeded. -/
def expectSqlError {α : Type} (what : String) (x : IO α) : IO SqlError := do
  match ← x.toBaseIO with
  | .ok _ => throw (IO.userError s!"{what} succeeded, but an error was expected")
  | .error e => return SqlError.ofIOError e

/-- The resident set size of this process in kB, from `/proc/self/status`; `none` where that does
not exist. -/
def rssKb : IO (Option Nat) := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    for line in status.splitOn "\n" do
      if line.startsWith "VmRSS:" then
        -- `VmRSS:\t  12345 kB`
        let fields := (line.drop 6).trimAscii.toString.splitOn " "
        return fields[0]? >>= String.toNat?
    return none
  catch _ =>
    return none

/-- A parameter of every kind a text-format parameter has to survive. -/
def specialValues : Array String :=
  #["", "it's", "a \"quoted\" word", "back\\slash \\\\ double", "semi; colon -- comment",
    "unicode: äöü ß € 日本語 🎉", "$1 $2 :: %s", "line\nbreak\ttab", "😀",
    String.ofList (List.replicate (1024 * 1024) 'x')]

def testParams (conn : Connection) : IO Unit := do
  -- Types are inferred from their use; `NULL` comes back as `none`.
  let res ← conn.queryParams "SELECT $1::text AS a, $2::int AS b, $3::text AS c, $4::int + 1 AS d"
    #[some "hello", none, some "", some "41"]
  check (res.columns == #["a", "b", "c", "d"]) s!"columns: {res.columns}"
  check (res.rows == #[#[some "hello", none, some "", some "42"]]) s!"rows: {repr res.rows}"
  check (res.affected == 1) s!"affected: {res.affected}"
  -- Special characters round-trip through a table, untouched by any quoting.
  _ ← conn.execParams "CREATE TEMP TABLE param_test (id int PRIMARY KEY, val text)" #[]
  let mut i := 0
  for value in specialValues do
    let n ← conn.execParams "INSERT INTO param_test (id, val) VALUES ($1, $2)"
      #[some (toString i), some value]
    check (n == 1) s!"insert {i} affected {n}"
    i := i + 1
  let n ← conn.execParams "INSERT INTO param_test (id, val) VALUES ($1, $2)"
    #[some (toString i), none]
  check (n == 1) "null insert"
  let back ← conn.queryParams "SELECT val FROM param_test ORDER BY id" #[]
  check (back.rows.size == specialValues.size + 1) s!"{back.rows.size} rows read back"
  for j in [0:specialValues.size] do
    check (back.rows[j]! == #[some specialValues[j]!]) s!"value {j} changed in transit"
  check (back.rows.back! == #[none]) "null read back"
  -- A parameter equal to the 1 MB string is looked up by value, so it went through unchanged.
  let hit ← conn.queryParams "SELECT id, length(val) FROM param_test WHERE val = $1"
    #[some specialValues.back!]
  check (hit.rows == #[#[some (toString (specialValues.size - 1)), some "1048576"]])
    s!"1 MB lookup: {repr hit.rows}"
  -- A statement affecting several rows reports the count; a `SELECT` reports its rows.
  let n ← conn.execParams "UPDATE param_test SET val = $1 WHERE id < $2" #[some "x", some "3"]
  check (n == 3) s!"update affected {n}"
  let n ← conn.execParams "DELETE FROM param_test" #[]
  check (n == specialValues.size + 1) s!"delete affected {n}"
  IO.println "  params: ok"

def testErrors (conn : Connection) : IO Unit := do
  _ ← conn.execParams "CREATE TEMP TABLE unique_test (k text UNIQUE)" #[]
  _ ← conn.execParams "INSERT INTO unique_test VALUES ($1)" #[some "a"]
  let e ← expectSqlError "duplicate insert" <|
    conn.execParams "INSERT INTO unique_test VALUES ($1)" #[some "a"]
  check e.isUniqueViolation s!"expected 23505, got {repr e}"
  check (e.message.startsWith "ERROR:") s!"message: {e.message}"
  let e ← expectSqlError "select from a missing table" <|
    conn.queryParams "SELECT * FROM no_such_table_here" #[]
  check e.isUndefinedTable s!"expected 42P01, got {repr e}"
  let e ← expectSqlError "syntax error" <| conn.queryParams "SELEC 1" #[]
  check (e.sqlstate == some "42601") s!"expected 42601, got {repr e}"
  -- The connection is still usable afterwards.
  let r ← conn.queryParams "SELECT 1" #[]
  check (r.rows == #[#[some "1"]]) "connection unusable after an error"
  -- The same through the `M` monad: the error is a value of the backend's exception type.
  let res ← M.run { connectionInfo := "", connection := conn } do
    execParams "INSERT INTO unique_test VALUES ($1)" #[some "a"]
  match res with
  | .error (.sqlError e) => check e.isUniqueViolation s!"M: expected 23505, got {repr e}"
  | .error e => throw (IO.userError s!"M: unexpected error {repr e}")
  | .ok _ => throw (IO.userError "M: duplicate insert succeeded")
  let res ← M.run { connectionInfo := "", connection := conn } do
    queryParams "SELECT k FROM unique_test WHERE k = $1" #[some "a"]
  match res with
  | .ok r => check (r.rows == #[#[some "a"]]) s!"M: rows {repr r.rows}"
  | .error e => throw (IO.userError s!"M: {repr e}")
  -- A failed transaction is rolled back and reported, not committed.
  let res ← M.run { connectionInfo := "", connection := conn } do
    DBMonadTransactional.withTransaction do
      _ ← execParams "INSERT INTO unique_test VALUES ($1)" #[some "b"]
      _ ← execParams "INSERT INTO unique_test VALUES ($1)" #[some "b"]
  match res with
  | .error (.sqlError e) => check e.isUniqueViolation s!"transaction: got {repr e}"
  | _ => throw (IO.userError "transaction: expected a unique violation")
  let r ← conn.queryParams "SELECT count(*) FROM unique_test" #[]
  check (r.rows == #[#[some "1"]]) s!"transaction not rolled back: {repr r.rows}"
  check (conn.transactionStatus == .idle) "transaction still open"
  IO.println "  errors: ok"

def testNotify (url : String) : IO Unit := do
  let listener ← Connection.open url
  let sender ← Connection.open url
  _ ← listener.execParams "LISTEN db_test_channel" #[]
  -- Nothing has been sent: the wait times out.
  let t0 ← IO.monoMsNow
  check (← listener.waitNotify 150).isNone "notification received before any was sent"
  let elapsed := (← IO.monoMsNow) - t0
  check (elapsed ≥ 140 && elapsed < 2000) s!"timeout took {elapsed} ms"
  check (← listener.notifies).isEmpty "notifications pending before any was sent"
  -- One notification, received with its payload and the sender's backend pid.
  let pid ← sender.queryParams "SELECT pg_backend_pid()" #[]
  let some (some pid) := pid.rows[0]?.bind (·[0]?) | throw (IO.userError "no backend pid")
  _ ← sender.execParams "SELECT pg_notify($1, $2)" #[some "db_test_channel", some "hello 🎉"]
  let some n ← listener.waitNotify 5000 | throw (IO.userError "no notification within 5 s")
  check (n.channel == "db_test_channel") s!"channel {n.channel}"
  check (n.payload == "hello 🎉") s!"payload {n.payload}"
  check (toString n.backendPid == pid) s!"backend pid {n.backendPid} vs {pid}"
  -- Several at once, drained without waiting; distinct payloads, since the server merges
  -- identical notifications of one transaction.
  _ ← sender.execParams
    "SELECT pg_notify('db_test_channel', 'one'), pg_notify('db_test_channel', 'two'), \
     pg_notify('db_test_channel', 'three')" #[]
  let mut got : Array Notification := #[]
  for _ in [0:50] do
    got := got ++ (← listener.notifies)
    if got.size ≥ 3 then break
    if let some n ← listener.waitNotify 1000 then got := got.push n
  check (got.map (·.payload) == #["one", "two", "three"]) s!"drained {repr got}"
  -- A different channel is not delivered.
  _ ← sender.execParams "NOTIFY db_test_other_channel" #[]
  check (← listener.waitNotify 100).isNone "received a notification of a channel not listened to"
  listener.close
  sender.close
  IO.println "  notify: ok"

def testLifecycle (url : String) : IO Unit := do
  let conn ← Connection.open url
  check (← conn.status) "fresh connection not ok"
  let version ← conn.serverVersion
  check (version ≥ 100000) s!"server version {version}"
  conn.reset
  check (← conn.status) "connection not ok after reset"
  check ((← conn.queryParams "SELECT 2 + 2" #[]).rows == #[#[some "4"]]) "query after reset"
  conn.close
  check (!(← conn.status)) "closed connection reports ok"
  conn.close
  match ← (conn.queryParams "SELECT 1" #[]).toBaseIO with
  | .ok _ => throw (IO.userError "query on a closed connection succeeded")
  | .error e =>
    check ((toString e).startsWith "the PostgreSQL connection has been closed")
      s!"closed connection error: {e}"
  match ← (Connection.open "postgresql://nobody:wrong@localhost:1/nowhere").toBaseIO with
  | .ok _ => throw (IO.userError "connecting to nowhere succeeded")
  | .error e => check ((toString e).startsWith "cannot connect to PostgreSQL:") s!"open error: {e}"
  match ← runDB "postgresql://nobody:wrong@localhost:1/nowhere" (pure ()) with
  | .error (.connectionError msg) =>
    check (msg.startsWith "cannot connect to PostgreSQL:") s!"runDB error: {msg}"
  | _ => throw (IO.userError "runDB to nowhere did not report a connection error")
  IO.println "  lifecycle: ok"

/-- Run `count` small statements and check that the resident set does not grow with them, which
it did while results were never `PQclear`ed. -/
def testMemory (conn : Connection) (count : Nat) : IO Unit := do
  let round (n : Nat) : IO Unit := do
    for i in [0:n] do
      let r ← conn.queryParams "SELECT $1::int + 1 AS n, repeat('x', 100) AS pad"
        #[some (toString i)]
      check (r.rows.size == 1) "memory round"
      _ ← conn.execParams "SELECT 1" #[]
      match ← conn.exec "SELECT 1" with
      | .data _ => pure ()
      | _ => throw (IO.userError "exec")
  -- Warm up, so that allocator growth on the first queries is not counted.
  round 500
  let some before ← rssKb | IO.println "  memory: skipped (no /proc/self/status)"; return
  round count
  let some after ← rssKb | return
  IO.println s!"  memory: RSS {before} kB before, {after} kB after {3 * count} statements"
  check (after ≤ before + 2048) s!"RSS grew by {after - before} kB"

def test : IO Unit := do
  let some url ← IO.getEnv "DB_TEST_URL"
    | IO.println "PostgreSQL tests skipped: DB_TEST_URL is not set."
  IO.println "PostgreSQL tests:"
  let conn ← Connection.open url
  testParams conn
  testErrors conn
  conn.close
  testNotify url
  testLifecycle url
  let count := ((← IO.getEnv "DB_TEST_QUERIES").bind String.toNat?).getD 10000
  let conn ← Connection.open url
  testMemory conn count
  conn.close
  IO.println "PostgreSQL tests passed."

end PostgresTests
