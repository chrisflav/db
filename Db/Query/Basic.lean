/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Std
import Db.Utils.VarChar

inductive DBType where
  | bool : DBType
  | int : DBType
  | varchar (n : Nat) : DBType
  deriving BEq, Repr, DecidableEq, Hashable

protected def DBType.Value : DBType → Type
  | .bool => Bool
  | .varchar n => VarChar n
  | .int => Int

structure Column where
  type : DBType
  deriving BEq, Repr

structure Table where
  columns : Std.HashMap String Column

structure Database where
  tables : Std.HashMap String Table

@[grind]
def Database.HasTable (d : Database) (name : String) : Prop :=
  name ∈ d.tables

@[grind]
def Table.HasColumn (t : Table) (name : String) : Prop :=
  name ∈ t.columns

structure Database.Ident (d : Database) where
  tableName : String
  columnName : String
  hasTable : d.HasTable tableName := by grind
  hasColumn : columnName ∈ d.tables[tableName].columns := by grind
  deriving BEq, Hashable
  -- btype_eq : d.tables[table].columns[column].btype = t := by grind

attribute [grind] Database.Ident.hasTable Database.Ident.hasColumn

def Database.Ident.table {d : Database} (i : d.Ident) : Table :=
  d.tables[i.tableName]'(by grind)

def Database.Ident.column {d : Database} (i : d.Ident) : Column :=
  ((d.tables[i.tableName]'(by grind)).columns)[i.columnName]'(by grind)

def Database.Ident.dbtype {d : Database} (i : d.Ident) : DBType :=
  i.column.type

def Database.Ident.toString {d : Database} (i : d.Ident) : String :=
  s!"{i.tableName}.{i.columnName}"

def Table.idents {d : Database} (tname : String) (ht : d.HasTable tname) : Std.HashSet d.Ident :=
  .ofList (d.tables[tname].columns.toList.pmap (P := fun a ↦ a ∈ d.tables[tname].columns.toList)
    (fun c hmem ↦ ⟨tname, c.1, ht, by grind⟩) (by grind))

instance (d : Database) (name : String) : Decidable (d.HasTable name) :=
  inferInstanceAs <| Decidable (name ∈ d.tables)

def Database.HasTable.get {d : Database} {name : String} (h : d.HasTable name) : Table :=
  d.tables[name]

def Database.HasColumn (d : Database) (table : String) (column : String) : Prop :=
  ∃ (h : d.HasTable table), column ∈ d.tables[table].columns

inductive DBExpr (d : Database) : DBType → Type 1 where
  | true : DBExpr d .bool
  | false : DBExpr d .bool
  | and (e₁ e₂ : DBExpr d .bool) : DBExpr d .bool
  | eq {t : DBType} (e₁ e₂ : DBExpr d t) : DBExpr d .bool
  | var (i : d.Ident) (t : DBType) : DBExpr d t
  | str {n : Nat} (s : VarChar n) : DBExpr d (.varchar n)

inductive Database.Name (d : Database) where
  | ident (i : d.Ident) : Name d
  | computation (n : String) (t : DBType) : Name d
  deriving BEq, Hashable

def Database.Name.dbtype {d : Database} : d.Name → DBType
  | .ident i => i.dbtype
  | .computation _ t => t

def Database.Name.toString {d : Database} : d.Name → String
  | .ident i => i.toString
  | .computation s _ => s

def Table.names {d : Database} (tname : String) (ht : d.HasTable tname := by grind) :
    Std.HashSet d.Name :=
  .ofList (d.tables[tname].columns.toList.pmap (P := fun a ↦ a ∈ d.tables[tname].columns.toList)
    (fun c hmem ↦ .ident ⟨tname, c.1, ht, by grind⟩) (by grind))

-- TODO: add join operations
/--
A query on the database `d` indexed over the (unique) names of the outputs.
-/
inductive Query (d : Database) : Std.HashSet d.Name → Type 1 where
  | all (table : String) (ht : d.HasTable table := by grind) : Query d (Table.names table ht)
  | filter {s : Std.HashSet d.Name} (q : Query d s) (e : DBExpr d .bool) : Query d s

def signature {d : Database} (s : Std.HashSet d.Name) : Std.HashMap d.Name DBType :=
  s.inner.map (fun n _ ↦ n.dbtype)

structure Database.Insert (d : Database) (tableName : String)
    (ht : d.HasTable tableName := by grind) where

/-
def authors : Table where
  columns := .ofList
    [⟨"id", ⟨.int⟩⟩,
     ⟨"name", ⟨.varchar 100⟩⟩,
     ⟨"modern", ⟨.bool⟩⟩]
-/

def fish : Table where
  columns := .ofList
    [⟨"name", ⟨.varchar 100⟩⟩, ⟨"length", ⟨.int⟩⟩]

abbrev database : Database where
  tables := .ofList
    [⟨"fish", fish⟩]

--example : Query database (Table.names "author") :=
--  .filter (.all "author") .true
