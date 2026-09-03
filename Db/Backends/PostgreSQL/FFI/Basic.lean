/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
namespace PostgreSQL

/-- A notification received from `LISTEN`, as sent by `NOTIFY channel, 'payload'`. -/
structure Notification where
  channel : String
  payload : String
  /-- The process id of the server backend that sent the notification. -/
  backendPid : Nat
  deriving Repr, BEq, Inhabited

namespace Internal

inductive ConnectionStatus where
  | CONNECTION_OK
  | CONNECTION_BAD

inductive ResultStatus where
  | EMPTY_QUERY
  | COMMAND_OK
  | TUPLES_OK
  | SINGLE_TUPLE
  | TUPLES_CHUNK
  | COPY_OUT
  | COPY_IN
  | COPY_BOTH
  | BAD_RESPONSE
  | NONFATAL_ERROR (msg : String)
  | FATAL_ERROR (msg : String)
  | PIPELINE_SYNC
  | PIPELINE_ABORTED
  deriving Repr

def kb (b : UInt64) : UInt64 := 1024 * b
def mb (b : UInt64) : UInt64 := 1048576 * b
def gb (b : UInt64) : UInt64 := 1073741824 * b

/-- A `PGconn`, closed by `PQfinish` when the Lean object is collected or `finish` is called.

libpq allows a connection to be used from one thread at a time, and the library does not lock, so
no two threads may use the same `Connection` concurrently. -/
opaque Connection : Type

/-- A `PGresult`, released by `PQclear` when the Lean object is collected. -/
opaque Result : Type

@[extern "c_PQconnectdb"]
opaque connect (connInfo : @& String) : IO Connection

/-- `CONNECTION_OK` is `0`; a closed connection reports `CONNECTION_BAD`, which is `1`. -/
@[extern "c_PQstatus"]
opaque Connection.connStatus (conn : @& Connection) : UInt8

/-- The most recent error message on the connection. -/
@[extern "c_PQerrorMessage"]
opaque Connection.errorMessage (conn : @& Connection) : String

/-- Close the connection now. A second call does nothing. -/
@[extern "c_PQfinish"]
opaque Connection.finish (conn : @& Connection) : IO Unit

/-- Close the connection and reopen it with the same parameters. -/
@[extern "c_PQreset"]
opaque Connection.reset (conn : @& Connection) : IO Unit

/-- The server version as an integer, e.g. `170004` for 17.4. -/
@[extern "c_PQserverVersion"]
opaque Connection.serverVersion (conn : @& Connection) : IO Nat

/-- The file descriptor of the connection's socket. -/
@[extern "c_PQsocket"]
opaque Connection.socket (conn : @& Connection) : IO Nat

@[extern "c_PQexec"]
opaque Connection.exec (m : @& Connection) (query : @& String) : IO Result

/-- Run `query` with `params` bound to `$1`, `$2`, ..., all in text format; `none` is `NULL`. -/
@[extern "c_PQexecParams"]
opaque Connection.execParams (m : @& Connection) (query : @& String)
    (params : @& Array (Option String)) : IO Result

@[extern "c_PQresultStatus"]
opaque Result.statusAsString (res : @& Result) : String

@[extern "c_PQresultErrorMessage"]
opaque Result.errorMessage (res : @& Result) : String

/-- One field of the error report, by its `PG_DIAG_*` code; empty if the result has no such
field. -/
@[extern "c_PQresultErrorField"]
opaque Result.errorField (res : @& Result) (fieldcode : UInt32) : String

/-- The `PG_DIAG_SQLSTATE` field code, the character `C`. -/
def PG_DIAG_SQLSTATE : UInt32 := 67

/-- Return the status of a result in terms of `ResultStatus`. -/
def Result.status (res : Result) : ResultStatus :=
  match res.statusAsString with
  | "PGRES_TUPLES_OK" => .TUPLES_OK
  | "PGRES_COMMAND_OK" => .COMMAND_OK
  | "PGRES_EMPTY_QUERY" => .EMPTY_QUERY
  | "PGRES_BAD_RESPONSE" => .BAD_RESPONSE
  | "PGRES_NONFATAL_ERROR" => .NONFATAL_ERROR res.errorMessage
  | _ => .FATAL_ERROR res.errorMessage

/-- The status of the transaction on a connection. -/
inductive TransactionStatus where
  | idle
  | active
  | inTransaction
  | inError
  | unknown
  deriving Repr, DecidableEq

@[extern "c_PQtransactionStatus"]
opaque Connection.transactionStatusCode (conn : @& Connection) : UInt8

def Connection.transactionStatus (conn : Connection) : TransactionStatus :=
  match conn.transactionStatusCode with
  | 0 => .idle
  | 1 => .active
  | 2 => .inTransaction
  | 3 => .inError
  | _ => .unknown

/-- The number of rows the statement affected, as a decimal string; empty for a statement to which
that does not apply. -/
@[extern "c_PQcmdTuples"]
opaque Result.cmdTuples (res : @& Result) : String

@[extern "c_PQntuples"]
opaque Result.ntuples (res : @& Result) : UInt32

@[extern "c_PQnfields"]
opaque Result.nfields (res : @& Result) : UInt32

@[extern "c_PQfname"]
opaque Result.fname (res : @& Result) (columnNumber : UInt32) : String

@[extern "c_PQftable"]
opaque Result.ftable (res : @& Result) (columnNumber : UInt32) : UInt32

@[extern "c_PQfnumber"]
opaque Result.fnumber (res : @& Result) (columnName : @& String) : Int32

@[extern "c_PQgetisnull"]
opaque Result.getisnull (res : @& Result) (rowNumber columNumber : UInt32) : UInt32

@[extern "c_PQgetlength"]
opaque Result.getlength (res : @& Result) (rowNumber columNumber : UInt32) : UInt32

-- TODO: change this to ByteArray or similar to support binary data
@[extern "c_PQgetvalue"]
opaque Result.getvalue (res : @& Result) (rowNumber columNumber : UInt32) : String

/-- Read whatever the server has sent without blocking. -/
@[extern "c_PQconsumeInput"]
opaque Connection.consumeInput (conn : @& Connection) : IO Unit

/-- The next notification libpq has already received, if any. Does not read from the socket;
call `consumeInput` first. -/
@[extern "c_PQnotifies"]
opaque Connection.notifies (conn : @& Connection) : IO (Option Notification)

/-- `consumeInput` followed by draining every notification received so far. -/
@[extern "c_PQnotifiesAll"]
opaque Connection.notifiesAll (conn : @& Connection) : IO (Array Notification)

/-- Wait up to `timeoutMs` milliseconds for a notification; `none` when the time is up. -/
@[extern "c_PQwaitNotify"]
opaque Connection.waitNotify (conn : @& Connection) (timeoutMs : UInt32) :
    IO (Option Notification)

end Internal

end PostgreSQL
