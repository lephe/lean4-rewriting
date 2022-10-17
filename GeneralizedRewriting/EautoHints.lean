
/-
## Hint databases and hint declaration
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

structure HintDescr where
  databaseName: Name
  hint: Hint

structure HintDB where
  name: Name
  hints: Array Hint

instance: ToMessageData HintDB where
  toMessageData db :=
    m!"in database {db.name}:\n  " ++
    MessageData.joinSep (db.hints.toList.map toMessageData) (.ofFormat "\n  ")

abbrev EautoDB := Array HintDB

-- TODO: I get some hints multiple times. Does persistence mean that imported
-- entries get transitively registered as entries of the current module? If so,
-- patch out `exportHints` to only export the hints created by `addHint`.

def EautoDB.addHint (dbs: EautoDB) (h: HintDescr): EautoDB :=
  match dbs.findIdx? (fun db => db.name = h.databaseName) with
  | some i =>
      dbs.modify i (fun db => { db with hints := db.hints.push h.hint })
  | none =>
      dbs.push ({ name := h.databaseName, hints := #[h.hint] })

def EautoDB.importHints (aah: Array (Array HintDescr)): ImportM EautoDB :=
  return aah.foldl (fun dbs ah => ah.foldl EautoDB.addHint dbs) #[]

def EautoDB.exportHints (dbs: EautoDB): Array HintDescr := Id.run do
  let mut ah := #[]
  for db in dbs do
    for hint in db.hints do
      ah := ah.push { databaseName := db.name, hint := hint }
  return ah

def EautoDB.getDB (dbs: EautoDB) (name: Name): CoreM HintDB :=
  match dbs.find? (fun db => db.name = name) with
  | some db => return db
  | none => throwError m!"no eauto database called {name}"

initialize eautoDatabaseExtension: PersistentEnvExtension HintDescr HintDescr EautoDB ←
  registerPersistentEnvExtension {
    mkInitial := return #[],
    addImportedFn := EautoDB.importHints,
    addEntryFn := EautoDB.addHint,
    exportEntriesFn := EautoDB.exportHints,
  }
