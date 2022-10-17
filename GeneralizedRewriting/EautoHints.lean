/-
## Hint databases and hint declaration

This module handles the registration, import and export of eauto hints.
-/

import Lean
open Lean Meta

namespace Eauto

inductive Hint where
  | Constant (n: Name)
  | Extern (term: Term) (tactic: TSyntax `tactic) (cost: Nat)

instance : ToMessageData Hint where
  toMessageData
    | .Constant n => n
    | .Extern term tactic cost => m!"Extern {cost}: {term} => {tactic}"

/-
A top-level command run by modules to create databases, add hints, etc. We keep
them inside .olean files using a persistent extensions so that hints are
retained between imports.
-/
inductive HintCommand where
  | CreateDB (name: Name)
  | CreateHint (databaseName: Name) (hint: Hint)

structure HintDB where
  name: Name
  hints: Array Hint

instance: ToMessageData HintDB where
  toMessageData db :=
    MessageData.joinSep (db.hints.toList.map toMessageData) (.ofFormat "\n  ")

-- We remember which commands are imported and which ones are original so we
-- are able to export only the originals
structure EautoDB where
  dbs: Array HintDB := #[]
  moduleCommands: Array HintCommand := #[]
deriving Inhabited

def EautoDB.findHintDB? (e: EautoDB) (name: Name): Option Nat :=
  e.dbs.findIdx? (fun db => db.name = name)

def EautoDB.hasHintDB (e: EautoDB) (name: Name): Bool :=
  e.findHintDB? name |>.isSome

-- We cannot throw errors at this level, so we let the top-level commands
-- handle it instead and do no-ops here.
def EautoDB.runCommand (e: EautoDB): HintCommand → EautoDB
  | .CreateDB name =>
      if e.hasHintDB name then e
      else { e with dbs := e.dbs.push { name := name, hints := #[] }}
  | .CreateHint dbName hint =>
      match e.findHintDB? dbName with
      | none => e
      | some i => { e with
          dbs := e.dbs.modify i (fun db => { db with hints := db.hints.push hint })}

def EautoDB.addCommand (e: EautoDB) (c: HintCommand): EautoDB :=
  let e' := e.runCommand c
  { e' with moduleCommands := e'.moduleCommands.push c }

def EautoDB.importCommands (comms: Array (Array HintCommand)): ImportM EautoDB :=
  return comms.foldl (fun dbs ac => ac.foldl EautoDB.runCommand dbs) {}

def EautoDB.exportCommands (e: EautoDB): Array HintCommand :=
  e.moduleCommands

def EautoDB.getDB (e: EautoDB) (name: Name): CoreM HintDB :=
  match e.dbs.find? (fun db => db.name = name) with
  | some db => return db
  | none => throwError m!"no eauto database called {name}"

initialize eautoDatabaseExtension: PersistentEnvExtension HintCommand HintCommand EautoDB ←
  registerPersistentEnvExtension {
    mkInitial := return {},
    addImportedFn := EautoDB.importCommands,
    addEntryFn := EautoDB.addCommand,
    exportEntriesFn := EautoDB.exportCommands,
  }
