/-
# Basic typeclass inference with backtracking

This file implements a very rough imitation of Coq's `eauto`. It is used to
close a set of goals (here: typeclass queries) that may share metavariables,
with backtracking and hints with priorities. Unlike the standard synthesis
algorithm, this will instantiate metavariables.

General idea to solve a goal:

1. Try to apply hypotheses from the local context; the "cost" is the number of
   parameters (subgoals, roughly). If one unifies, solve subgoals recursively.
   Depending on whether we solve normally (`eauto`) or as a custom typeclass
   algorithm (`typeclasses_eauto`), typeclass parameters are either synthesized
   immediately or left as subgoals.

2. Try to apply hints from provided databases. These can be:
   - Constant hints, ie. theorems. The method is the same as for hypotheses.
   - Extern hints (a pattern + a tactic + a fixed cost).

3. When solving as a custom typeclass algorithm, try instances given by
   `SynthInstance.getInstances` (ie. instances that unify with the goal).

4. Recursively solve all the subgoals *and* the entire pending stack (which is
   affected by current decisions due to metavariables being unified). If that
   fails, backtrack to the next applicable hint.

5. If not hint applies or a pre-determined maximum depth is reached, fail.

Future wishlist:
- Caching. There is *a ton* of redundant work during backtracking.
  This requires being smart with metavariables, since the same "goal" can be
  traversed with different metavariables assignments.
- A rough idea of when/why this algorithm will fail to find solutions that
  `Lean.Meta.SynthInstance` finds.
- Solve the most egregious performance issues.

Realistic TODO list:
- TODO: Sort hypotheses, constant hints and typeclass instances by priority
  based on `getExpectedNumArgs`.
- TODO: Figure out how to apply extern hints
-/

import Lean
import GeneralizedRewriting.EautoHints

open Lean Meta Elab Tactic

/-
## apply_no_synth

This variant of `apply` does not try to solve implicit instances by typeclass
resolution, and instead adds them as subgoals. It also ignores dependent
subgoals and case naming (for the purpose of `eauto`).
-/

namespace ApplyNoSynth

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
  throwTacticEx `apply mvarId m!"failed to unify{indentExpr eType}\nwith{indentExpr targetType}"

private def dependsOnOthers (mvar : Expr) (otherMVars : Array Expr) : MetaM Bool :=
  otherMVars.anyM fun otherMVar => do
    if mvar == otherMVar then
      return false
    else
      let otherMVarType ← inferType otherMVar
      return (otherMVarType.findMVar? fun mvarId => mvarId == mvar.mvarId!).isSome

private def getNonDependentMVars (mvars : Array Expr) : MetaM (Array MVarId) := do
  let mut nonDeps := #[]
  for mvar in mvars do
    if !(← dependsOnOthers mvar mvars) then
      nonDeps := nonDeps.push mvar.mvarId!
  return nonDeps

def _root_.Lean.MVarId.applyNoSynth (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `apply
    let targetType ← mvarId.getType
    let eType      ← inferType e
    let mut (numArgs, hasMVarHead) ← getExpectedNumArgsAux eType
    unless hasMVarHead do
      let targetTypeNumArgs ← getExpectedNumArgs targetType
      numArgs := numArgs - targetTypeNumArgs
    let (newMVars, _, eType) ← forallMetaTelescopeReducing eType (some numArgs)
    unless (← isDefEq eType targetType) do throwApplyError mvarId eType targetType
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    let otherMVarIds ← getMVarsNoDelayed e
    let newMVarIds := (← getNonDependentMVars newMVars) |>.toList
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result

end ApplyNoSynth

/-
## eauto hint commands
-/

namespace Eauto

elab "#print_eauto_db": command => do
  let env ← getEnv
  let e := eautoDatabaseExtension.getState env
  if e.dbs.size == 0 then
    logInfo "no hint databases"
  else
    logInfo (MessageData.joinSep (e.dbs.toList.map fun db =>
        m!"in database {db.name}:\n  " ++ toMessageData db)
      (.ofFormat "\n\n"))

elab "eauto_create_db" dbname:ident: command => do
  let env ← getEnv
  let e := eautoDatabaseExtension.getState env

  if e.hasHintDB dbname.getId then
    throwError "eauto database {dbname} already exists"
  else
    setEnv (eautoDatabaseExtension.addEntry env <| .CreateDB dbname.getId)

elab "eauto_hint " cst:ident ":" dbname:ident: command => do
  let env ← getEnv
  let e := eautoDatabaseExtension.getState env
  let hint: Hint ←
    match env.find? cst.getId with
    | some _ => pure <| Hint.Constant cst.getId
    | none => throwError "no such constant {cst}"

  if ! e.hasHintDB dbname.getId then
    throwError "no eauto database {dbname}"
  setEnv (eautoDatabaseExtension.addEntry env <| .CreateHint dbname.getId hint)

end Eauto

/-
## `eauto` and `typeclasses_eauto`
-/

namespace Eauto

initialize
  registerTraceClass `Meta.Tactic.eauto
  registerTraceClass `Meta.Tactic.eauto.goals
  registerTraceClass `Meta.Tactic.eauto.hints
  registerTraceClass `Meta.Tactic.eauto.instances

initialize
  eautoFailedExceptionId : InternalExceptionId ← registerInternalExceptionId `eautoFailed

structure Context where
  hintDatabases: Array HintDB
  useTypeclasses: Bool
  maximumDepth: Nat

abbrev EautoM := ReaderT Context MetaM

def ppSubgoals (subgoals: List MVarId): EautoM MessageData :=
  let ppOne (m: MVarId) := do
    -- return toMessageData m -- to print hypotheses
    return m!"{← ppExpr (← m.getType)}"
  return MessageData.joinSep (← subgoals.mapM ppOne) (.ofFormat ", ")

instance : MonadBacktrack Meta.SavedState EautoM where
  saveState := Meta.saveState
  restoreState s := s.restore

private def throwEautoFailedEx: EautoM Unit :=
  throw <| Exception.internal eautoFailedExceptionId

private def apply' (goal: MVarId) (expr: Expr) (synthInstances: Bool): EautoM (List MVarId) :=
  if synthInstances then
    goal.apply expr
  else
    goal.applyNoSynth expr

mutual
partial def solve (goalMVar: MVarId) (depth: Nat) (goalStack: List (Nat × MVarId)): EautoM Unit := do
  let ctx ← read

  -- Intro any new binders
  let (new_fvars, goalMVar) ← goalMVar.intros
  let goalType ← goalMVar.getType

  goalMVar.withContext do
    if new_fvars.size > 0 then
      -- TODO: pp.inaccessibleNames doesn't show the names with tombstones?
      withOptions (pp.sanitizeNames.set . false) do
        trace[Meta.Tactic.eauto] "intros {new_fvars.size} binders: {goalMVar}"

    -- Try hypotheses
    for ldecl in ← getLCtx do
      if ! ldecl.isAuxDecl then
        try
          commitIfNoEx do
            let t ← inferType ldecl.toExpr
            let subgoals ← apply' goalMVar ldecl.toExpr !ctx.useTypeclasses
            trace[Meta.Tactic.eauto.hints] "applying hypothesis: {ldecl.userName}: {← ppExpr t}"
            if subgoals != [] then
              trace[Meta.Tactic.eauto.hints] "subgoals: {← ppSubgoals subgoals}"
            -- Proceed to the subgoals or the next goal; in case of failure,
            -- attempt other hints
            solveNext (subgoals.map (depth+1, ·) ++ goalStack)
            return ()
        catch _ => pure ()

    -- Try database hints
    for db in ctx.hintDatabases do
      for hint in db.hints do
        try
          commitIfNoEx do
            match hint with
            | .Constant name =>
                let expr ← mkConstWithFreshMVarLevels name
                let type ← inferType expr
                let subgoals ← apply' goalMVar expr !ctx.useTypeclasses
                trace[Meta.Tactic.eauto.hints] "[{db.name}] applying hint: {hint}: {type}"
                if subgoals != [] then
                  trace[Meta.Tactic.eauto.hints] "subgoals: {← ppSubgoals subgoals}"
                solveNext (subgoals.map (depth+1, ·) ++ goalStack)
                return ()
            | .Extern _ _ _ =>
                -- TODO: Apply extern hints
                pure ()
        catch _ => pure ()

    -- Try typeclass instances
    if ctx.useTypeclasses && (← isClass? goalType).isSome then
      let instances ← SynthInstance.getInstances goalType
      trace[Meta.Tactic.eauto.instances] "instances: {instances}"
      for inst in instances do
        try
          commitIfNoEx do
            let subgoals ← apply' goalMVar inst !ctx.useTypeclasses
            trace[Meta.Tactic.eauto.hints] "applying instance: {inst}: {← ppExpr (← inferType inst)}"
            if subgoals != [] then
              trace[Meta.Tactic.eauto.hints] "subgoals: {← ppSubgoals subgoals}"
            solveNext (subgoals.map (depth+1, ·) ++ goalStack)
            return ()
        catch _ => pure ()

    if (← getExprMVarAssignment? goalMVar).isNone then
      trace[Meta.Tactic.eauto] "failed to close the goal"
      throwEautoFailedEx

partial def solveNext: List (Nat × MVarId) → EautoM Unit
  | [] => pure ()
  | (depth, goal) :: stack => do
      if ← goal.isAssigned then
        solveNext stack
      else
        let ctx ← read
        let goal_type ← instantiateMVars (← goal.getType)
        withTraceNode `Meta.Tactic.eauto
          (fun _ => return m!"goal[{depth}]: {goal_type}") do

          if depth > ctx.maximumDepth then
            trace[Meta.Tactic.eauto] "maximum depth exceeded"
            throwEautoFailedEx
          solve goal depth stack
end

def eautoCore (initialGoals: List MVarId): EautoM Unit :=
  solveNext (initialGoals.map (0, ·))

def eautoMain (goals: List MVarId) (dbNames: Array Name) (useTypeclasses: Bool): TacticM Bool := do
  let env ← getEnv
  let db := eautoDatabaseExtension.getState env

  let eautoCtx: Context := {
    hintDatabases := ← dbNames.mapM (EautoDB.getDB db ·)
    useTypeclasses := useTypeclasses
    maximumDepth := 5
  }

  try commitIfNoEx (Eauto.eautoCore goals |>.run eautoCtx)
  catch _ => pure ()

  let success ← goals.allM (fun m => do return (← getExprMVarAssignment? m).isSome)
  if !success then
    trace[Meta.Tactic.eauto] "no proof found"
  return success

end Eauto

elab "eauto" : tactic => do
  let _ ← Eauto.eautoMain [← getMainGoal] #[] false

elab "typeclasses_eauto" : tactic => do
  let _ ← Eauto.eautoMain [← getMainGoal] #[] true

elab "eauto" "with" dbs:ident+ : tactic => do
  let _ ← Eauto.eautoMain [← getMainGoal] (dbs.map TSyntax.getId) false

elab "typeclasses_eauto" "with" dbs:ident+ : tactic => do
  let _ ← Eauto.eautoMain [← getMainGoal] (dbs.map TSyntax.getId) true
