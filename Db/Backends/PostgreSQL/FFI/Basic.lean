/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
namespace PostgreSQL.Internal

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

opaque Connection : Type

opaque Result : Type

@[extern "c_PQconnectdb"]
opaque connect (connInfo : String) : IO Connection

@[extern "c_PQstatus"]
opaque Connection.connStatus (conn : Connection) : UInt8

@[extern "c_PQexec"]
opaque Connection.exec (m : Connection) (query : String) : IO Result

@[extern "c_PQresultStatus"]
opaque Result.statusAsString (res : Result) : String

@[extern "c_PQresultErrorMessage"]
opaque Result.errorMessage (res : Result) : String

/-- Return the status of a result in terms of `ResultStatus`. -/
def Result.status (res : Result) : ResultStatus :=
  match res.statusAsString with
  | "PGRES_TUPLES_OK" => .TUPLES_OK
  | "PGRES_COMMAND_OK" => .COMMAND_OK
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
opaque Connection.transactionStatusCode (conn : Connection) : UInt8

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
opaque Result.cmdTuples (res : Result) : String

@[extern "c_PQntuples"]
opaque Result.ntuples (res : Result) : UInt32

@[extern "c_PQnfields"]
opaque Result.nfields (res : Result) : UInt32

@[extern "c_PQfname"]
opaque Result.fname (res : Result) (columnNumber : UInt32) : String

@[extern "c_PQftable"]
opaque Result.ftable (res : Result) (columnNumber : UInt32) : UInt32

@[extern "c_PQfnumber"]
opaque Result.fnumber (res : Result) (columnName : String) : Int32

@[extern "c_PQgetisnull"]
opaque Result.getisnull (res : Result) (rowNumber columNumber : UInt32) : UInt32

@[extern "c_PQgetlength"]
opaque Result.getlength (res : Result) (rowNumber columNumber : UInt32) : UInt32

-- TODO: change this to ByteArray or similar to support binary data
@[extern "c_PQgetvalue"]
opaque Result.getvalue (res : Result) (rowNumber columNumber : UInt32) : String

end PostgreSQL.Internal
