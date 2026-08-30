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

/-- A handle for a connection to a PostgreSQL database. -/
structure Connection : Type where
  raw : Internal.Connection

-- TODO: make this return an error message in the case of failure
/-- Connect to the database described by the connection info string. If the connection succeeds,
returns this connection, otherwise returns `none`. -/
def connect (connInfo : String) : IO (Option Connection) := do
  let conn ← Internal.connect connInfo
  if conn.connStatus == 0 then
    return some { raw := conn }
  else
    return none

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
  | success
  | data (data : ResultData)
  | failure (error : ResultError)

/-- Execute a query on the given connection. -/
def Connection.exec (conn : Connection) (query : String) : IO Result := do
  let res ← conn.raw.exec query
  match res.status with
  | .TUPLES_OK => return .data { raw := res }
  | .COMMAND_OK => return .success
  | .NONFATAL_ERROR msg => return .failure (.nonfatal msg)
  | .FATAL_ERROR msg => return .failure (.fatal msg)
  | .EMPTY_QUERY => return .failure .emptyQuery
  | .BAD_RESPONSE => return .failure .badResponse
  | status =>
    IO.println s!"{repr status}"
    return .failure (.fatal "No error message.")

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
