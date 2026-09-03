/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Std
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic
import Db.Backends.PostgreSQL.FFI.Basic
import Db.Utils.FromString

def Fin.range (n : Nat) : List (Fin n) :=
  (List.range n).pmap (P := fun x ↦ x ∈ List.range n) (fun k hk ↦ ⟨k, by grind⟩) (by simp)

namespace PostgreSQL

/-- An error the server reported for a statement, or a failure of the connection itself.

`sqlstate` is the five-character SQLSTATE of a server error, e.g. `23505` for a unique violation
or `40001` for a serialisation failure; a connection-level failure (a lost connection, an out of
memory condition in libpq) has none. -/
structure SqlError where
  message : String
  sqlstate : Option String := none
  deriving Repr, BEq, Inhabited

namespace SqlError

/-- SQLSTATE `23505`: an insert or update violated a unique constraint. -/
def isUniqueViolation (e : SqlError) : Bool :=
  e.sqlstate == some "23505"

/-- SQLSTATE `40001`: the transaction has to be retried. -/
def isSerializationFailure (e : SqlError) : Bool :=
  e.sqlstate == some "40001"

/-- SQLSTATE `40P01`: the transaction was chosen as a deadlock victim and has to be retried. -/
def isDeadlockDetected (e : SqlError) : Bool :=
  e.sqlstate == some "40P01"

/-- SQLSTATE `42P01`: a relation the statement names does not exist. -/
def isUndefinedTable (e : SqlError) : Bool :=
  e.sqlstate == some "42P01"

instance : ToString SqlError where
  toString e :=
    match e.sqlstate with
    | some s => s!"SQLSTATE {s}: {e.message.trimAsciiEnd.toString}"
    | none => e.message.trimAsciiEnd.toString

/-- The `IO.Error` the `IO`-level API raises for `e`; `ofIOError` reads it back. -/
def toIOError (e : SqlError) : IO.Error :=
  .userError (toString e)

/-- Recover the error the `IO`-level API raised, parsing back the SQLSTATE `toIOError` put in front
of the message. Any other `IO.Error` becomes an error without a SQLSTATE. -/
def ofIOError (e : IO.Error) : SqlError :=
  let s := toString e
  if s.startsWith "SQLSTATE " && (s.drop 14).startsWith ": " then
    { message := (s.drop 16).toString, sqlstate := some ((s.drop 9).take 5).toString }
  else
    { message := s }

end SqlError

/-- A handle for a connection to a PostgreSQL database.

libpq allows a connection to be used from one thread at a time, and this library takes no locks, so
no two threads may use the same `Connection` concurrently; hand each thread (or each `Task`) its
own connection, e.g. from a pool. The connection is closed when the handle is garbage collected or
`close` is called, whichever comes first. -/
structure Connection : Type where
  raw : Internal.Connection

/-- Open a connection to the database described by the libpq connection string `conninfo`, e.g.
`postgresql://user:password@host/database`. Raises an `IO.Error` carrying libpq's message if the
connection cannot be established. -/
def Connection.open (conninfo : String) : IO Connection := do
  let raw ← Internal.connect conninfo
  if raw.connStatus != 0 then
    let message := raw.errorMessage.trimAsciiEnd.toString
    raw.finish
    throw (IO.userError s!"cannot connect to PostgreSQL: {message}")
  return { raw := raw }

/-- Connect to the database described by the connection info string. If the connection succeeds,
returns this connection, otherwise returns `none`; `Connection.open` reports why. -/
def connect (connInfo : String) : IO (Option Connection) := do
  try
    return some (← Connection.open connInfo)
  catch _ =>
    return none

/-- Whether the connection is usable (`CONNECTION_OK`). A closed connection is not. -/
def Connection.status (conn : Connection) : IO Bool :=
  return conn.raw.connStatus == 0

/-- The most recent error message libpq recorded on the connection. -/
def Connection.errorMessage (conn : Connection) : IO String :=
  return conn.raw.errorMessage.trimAsciiEnd.toString

/-- Close the connection and reopen it with the same parameters, e.g. after the server restarted.
Raises if the new connection could not be established. -/
def Connection.reset (conn : Connection) : IO Unit := do
  conn.raw.reset
  unless ← conn.status do
    throw (IO.userError s!"cannot reconnect to PostgreSQL: {← conn.errorMessage}")

/-- The server version as an integer, e.g. `170004` for 17.4. -/
def Connection.serverVersion (conn : Connection) : IO Nat :=
  conn.raw.serverVersion

/-- Close the connection now rather than when the handle is garbage collected. Closing an already
closed connection does nothing; any other use of it raises. -/
def Connection.close (conn : Connection) : IO Unit :=
  conn.raw.finish

/-- The server error `res` reports, if it reports one. Every status other than `TUPLES_OK` and
`COMMAND_OK` counts as a failure, including an empty query and the `COPY` states, which this API
does not drive. -/
def Internal.Result.error? (res : Internal.Result) : Option SqlError :=
  match res.statusAsString with
  | "PGRES_TUPLES_OK" | "PGRES_COMMAND_OK" => none
  | status =>
    let sqlstate := res.errorField Internal.PG_DIAG_SQLSTATE
    let message := res.errorMessage.trimAsciiEnd.toString
    some
      { message := if message.isEmpty then s!"unexpected result status {status}" else message
        sqlstate := if sqlstate.isEmpty then none else some sqlstate }

/-- Run `sql` through `PQexec`, which accepts several `;`-separated statements, and report a
failure as a value rather than an exception. -/
def Connection.execE (conn : Connection) (sql : String) :
    IO (Except SqlError Internal.Result) := do
  try
    let res ← conn.raw.exec sql
    match res.error? with
    | some e => return .error e
    | none => return .ok res
  catch e =>
    return .error { message := toString e }

/-- Run `sql` through `PQexecParams` with `params` bound to `$1`, `$2`, ..., and report a failure
as a value rather than an exception. -/
def Connection.execParamsE (conn : Connection) (sql : String) (params : Array (Option String)) :
    IO (Except SqlError Internal.Result) := do
  try
    let res ← conn.raw.execParams sql params
    match res.error? with
    | some e => return .error e
    | none => return .ok res
  catch e =>
    return .error { message := toString e }

/-- The rows a statement returned, in text format, and the number of rows it affected. -/
structure QueryResult where
  /-- The column names, in the order of the rows' entries. -/
  columns : Array String
  /-- The rows; a `none` entry is SQL's `NULL`. -/
  rows : Array (Array (Option String))
  /-- The number of rows the statement affected, as libpq's command tag reports it: for a `SELECT`
  the number of rows returned, `0` for a statement to which the notion does not apply. -/
  affected : Nat
  deriving Repr, Inhabited

/-- Read a successful result into a `QueryResult`. -/
def QueryResult.ofRaw (res : Internal.Result) : QueryResult :=
  let ncols := res.nfields
  let nrows := res.ntuples
  { columns := (Array.range ncols.toNat).map fun j => res.fname j.toUInt32
    rows := (Array.range nrows.toNat).map fun i =>
      (Array.range ncols.toNat).map fun j =>
        if res.getisnull i.toUInt32 j.toUInt32 == 1 then none
        else some (res.getvalue i.toUInt32 j.toUInt32)
    affected := res.cmdTuples.toNat?.getD 0 }

/-- Run `sql` with `params` bound to `$1`, `$2`, ... and return the rows.

Every parameter is sent as text and `none` is `NULL`; the server infers the parameters' types from
their use, so where that is ambiguous a cast such as `$1::int` says which. Parameters never take
part in SQL parsing, so a value needs no escaping whatever it contains. One statement per call: the
extended protocol behind `PQexecParams` does not accept several `;`-separated ones. A failure
raises the `IO.Error` of `SqlError.toIOError`; `SqlError.ofIOError` recovers its SQLSTATE. -/
def Connection.queryParams (conn : Connection) (sql : String) (params : Array (Option String)) :
    IO QueryResult := do
  match ← conn.execParamsE sql params with
  | .ok res => return .ofRaw res
  | .error e => throw e.toIOError

/-- Run `sql` with `params` bound to `$1`, `$2`, ... and return the number of rows it affected, as
`QueryResult.affected` reports it. -/
def Connection.execParams (conn : Connection) (sql : String) (params : Array (Option String)) :
    IO Nat := do
  match ← conn.execParamsE sql params with
  | .ok res => return res.cmdTuples.toNat?.getD 0
  | .error e => throw e.toIOError

/-- Wait up to `timeoutMs` milliseconds for a notification on a channel the connection has run
`LISTEN` for. Returns `none` when the time is up. Implemented with `poll()` on the connection's
socket, so the thread sleeps rather than spins; it blocks the OS thread for that long, so call it
from a dedicated task. -/
def Connection.waitNotify (conn : Connection) (timeoutMs : UInt32) : IO (Option Notification) :=
  conn.raw.waitNotify timeoutMs

/-- Read what the server has sent so far and return every notification among it, without waiting.
Notifications also arrive as a side effect of running any statement, so calling this after a query
returns what came in with it. -/
def Connection.notifies (conn : Connection) : IO (Array Notification) :=
  conn.raw.notifiesAll

/-- The result of a database query. -/
structure ResultData : Type where
  raw : Internal.Result

inductive ResultError where
  | emptyQuery
  | badResponse
  | fatal (msg : String)
  | nonfatal (msg : String)
  deriving Repr

inductive Result where
  /-- A statement that returned no rows, together with the number of rows it affected. -/
  | success (affected : Nat)
  | data (data : ResultData)
  | failure (error : ResultError)

/-- Execute a query on the given connection. Raises an `IO.Error` only if libpq produced no result
at all (the connection is closed or lost); a server error is a `.failure`. -/
def Connection.exec (conn : Connection) (query : String) : IO Result := do
  let res ← conn.raw.exec query
  match res.status with
  | .TUPLES_OK => return .data { raw := res }
  | .COMMAND_OK => return .success (res.cmdTuples.toNat?.getD 0)
  | .NONFATAL_ERROR msg => return .failure (.nonfatal msg)
  | .FATAL_ERROR msg => return .failure (.fatal msg)
  | .EMPTY_QUERY => return .failure .emptyQuery
  | .BAD_RESPONSE => return .failure .badResponse
  | status => return .failure (.fatal s!"unexpected result status {repr status}")

/-- The status of the transaction on this connection. -/
def Connection.transactionStatus (conn : Connection) : Internal.TransactionStatus :=
  conn.raw.transactionStatus

/-- The number of returned rows of a result data. -/
def ResultData.nrows (data : ResultData) : Nat :=
  data.raw.ntuples.toNat

/-- The number of returned rows of a result data. -/
def ResultData.ncolumns (data : ResultData) : Nat :=
  data.raw.nfields.toNat

/-- The name of the `columNumber`-th column. -/
def ResultData.columnName (data : ResultData) (columnNumber : Fin data.ncolumns) : String :=
  data.raw.fname columnNumber.val.toUInt32

/-- Returns if the field at the given index is null. -/
def ResultData.isNull (data : ResultData) (rowNumber : Fin data.nrows)
      (columnNumber : Fin data.ncolumns) : Bool :=
  data.raw.getisnull rowNumber.val.toUInt32 columnNumber.val.toUInt32 == 1

/-- The raw string value of the given field. -/
def ResultData.rawValue (data : ResultData) (rowNumber : Fin data.nrows)
      (columnNumber : Fin data.ncolumns) : String :=
  data.raw.getvalue rowNumber.val.toUInt32 columnNumber.val.toUInt32

/-- A possible PostgreSQL value. -/
inductive Value where
  | bool (b : Bool)
  | string (s : String)
  | int (n : Int)
  | raw (s : String)
  deriving BEq, Repr, Hashable

instance : ToString Value where
  toString
  | .bool b => toString b
  | .string s => s
  | .int n => toString n
  | .raw s => s!"raw({s})"

open Lean

-- TODO: instead of returning `raw`, return the cast `Value`
instance : FromJson Value where
  fromJson?
    | .null => .error "Not implemented!"
    | .bool b => .ok <| .bool b
    | .num _ => .ok (.raw "foo")
    | .str s => .ok <| .string s
    | _ => .error "Not a simple type."

def Value.fromString (s : String) : Value :=
  let x : Except String Value := do FromJson.fromJson? (← Json.parse s)
  match x with
  | .error _ => .raw s
  | .ok a => a

/-- The parsed value of the given field. -/
def ResultData.value (data : ResultData) (rowNumber : Fin data.nrows)
    (columnNumber : Fin data.ncolumns) : Value :=
  .fromString (data.rawValue rowNumber columnNumber)

/-- The parsed value of the given field. -/
def ResultData.valueWithExpectedType (data : ResultData) (rowNumber : Fin data.nrows)
    (columnNumber : Fin data.ncolumns) (α : Type) [FromString α] :
    Option α :=
  FromString.fromString (data.rawValue rowNumber columnNumber)

/-- The map `ColumnName → Value` of the `rowNumber`-th row. -/
def ResultData.row (data : ResultData) (rowNumber : Fin data.nrows) :
    Std.HashMap String Value := Id.run <| do
  let mut map := .emptyWithCapacity
  for i in Fin.range data.ncolumns do
    map := map.insert (data.columnName i) (data.value rowNumber i)
  return map

/-- The map `ColumnName → Value` of the `rowNumber`-th row. -/
def ResultData.rawRow (data : ResultData) (rowNumber : Fin data.nrows) :
    Std.HashMap String String := Id.run <| do
  let mut map := .emptyWithCapacity
  for i in Fin.range data.ncolumns do
    map := map.insert (data.columnName i) (data.rawValue rowNumber i)
  return map

/-- The map `ColumnName → Value` of the `rowNumber`-th row, in which `none` is SQL's `NULL`.

libpq reports a `NULL` field as the empty string, so the null flag is the only way to tell it
apart from a genuinely empty value. -/
def ResultData.optRow (data : ResultData) (rowNumber : Fin data.nrows) :
    Std.HashMap String (Option String) := Id.run <| do
  let mut map := .emptyWithCapacity
  for i in Fin.range data.ncolumns do
    map := map.insert (data.columnName i)
      (if data.isNull rowNumber i then none else some (data.rawValue rowNumber i))
  return map

/-- The array of all rows in `data`. -/
def ResultData.rawRows (data : ResultData) : Array (Std.HashMap String String) :=
  (Fin.range data.nrows).toArray.map (fun i ↦ data.rawRow i)

/-- The array of all rows in `data`, in which `none` is SQL's `NULL`. -/
def ResultData.optRows (data : ResultData) : Array (Std.HashMap String (Option String)) :=
  (Fin.range data.nrows).toArray.map (fun i ↦ data.optRow i)

/-- The array of all rows in `data`. -/
def ResultData.rows (data : ResultData) : Array (Std.HashMap String Value) :=
  (Fin.range data.nrows).toArray.map (fun i ↦ data.row i)

/-- The map `ColumnName → Array Value`, where each value is the list of all rows of the given
column. -/
def ResultData.columns (data : ResultData) : Std.HashMap String (Array Value) := Id.run <| do
  let mut map := .emptyWithCapacity
  for i in Fin.range data.ncolumns do
    map := map.insert
      (data.columnName i)
      ((Fin.range data.nrows).toArray.map (fun j ↦ data.value j i))
  return map

end PostgreSQL
