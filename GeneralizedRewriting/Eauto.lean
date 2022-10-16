/-
# Basic typeclass inference with backtracking

This file implements a very rough imitation of Coq's `eauto`. It is used to
close a set of goals (here: typeclass queries) that may share metavariables,
with backtracking and hints with priorities. Unlike the standard synthesis
algorithm, this will instantiate metavariables.

General idea to solve a goal:

1. Reduce it to WHNF (different visibility options could be considered)

2. Select hints based on the shape of the goal. Hints are:

   - Pre-selected constants, when they unify with the goal. This most notably
     includes hypotheses. The cost is the number of subgoals that applying them
     would generate.

   - External hints (a pattern + a tactic + a cost) if the pattern unifies with
     the goal. The cost is provided by the hint.

   - For typeclasses: instances given by `Lean.Meta.SynthInstance.getInstances`
     (ie. ones that unify with the goal). The cost is computed like constants.

3. Try all the hints that apply in increasing order of cost.

4. Recursively solve all the subgoals that get generated.

5. If not hint applies or a pre-determined maximum depth is reached, fail.

Wishlist:
- Caching. There is *a ton* of redundant work during backtracking.
  This requires being smart with metavariables, since the same "goal" can be
  traversed with different metavariables assignments.
- A rough idea of when/why this algorithm will fail to find solutions that
  `Lean.Meta.SynthInstance` finds.
- Solve the most egregious performance issues.

Current state (basically assumption):
TODO: Sort constant hints by priority (determining the priority requires
      applying them; potentially unifiying metavars... is there a simpler
      measure like the number of dependent hypotheses?)
TODO: Figure out how to apply extern hints
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
  let dbs := eautoDatabaseExtension.getState env
  if dbs.size == 0 then
    logInfo "no hint databases"
  else
    logInfo (MessageData.joinSep (dbs.toList.map toMessageData) (.ofFormat "\n\n"))

elab "eauto_hint " cst:ident ":" dbname:ident: command => do
  let env ← getEnv
  let hint: Hint ←
    match env.find? cst.getId with
    | some decl => pure <| Hint.Constant cst.getId decl.value! decl.type
    | none => throwError "no such constant {cst}"

  setEnv (eautoDatabaseExtension.addEntry env {
    databaseName := dbname.getId,
    hint := hint,
  })

end Eauto

/-
## `eauto` and `typeclasses_eauto`
-/

namespace Eauto

initialize
  registerTraceClass `Meta.Tactic.eauto
  registerTraceClass `Meta.Tactic.eauto.goals
  registerTraceClass `Meta.Tactic.eauto.hints

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

  goalMVar.withContext do
    if new_fvars.size > 0 then
      -- TODO: pp.inaccessibleNames doesn't show the names with tombstones?
      withOptions (pp.sanitizeNames.set . false) do
        trace[Meta.Tactic.eauto] "intros {new_fvars.size} binders: {goalMVar}"

    -- Check hypotheses
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

    for db in ctx.hintDatabases do
      for hint in db.hints do
        try
          commitIfNoEx do
            match hint with
            | .Constant _ expr _ =>
                let subgoals ← apply' goalMVar expr !ctx.useTypeclasses
                trace[Meta.Tactic.eauto.hints] "[{db.name}] applying hint: {hint}"
                if subgoals != [] then
                  trace[Meta.Tactic.eauto.hints] "subgoals: {← ppSubgoals subgoals}"
                -- If we manage to solve this goal and all the stack, return
                solveNext (subgoals.map (depth+1, ·) ++ goalStack)
                return ()
            | _ => pure ()
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

def eautoMain (dbNames: Array Name) (useTypeclasses: Bool): TacticM Unit := do
  let env ← getEnv
  let db := eautoDatabaseExtension.getState env

  withMainContext do
    let goalMVar ← getMainGoal

    let eautoCtx: Context := {
      hintDatabases := ← dbNames.mapM (EautoDB.getDB db ·)
      useTypeclasses := useTypeclasses
      maximumDepth := 5
    }

    -- Solve a single goal
    try commitIfNoEx (Eauto.eautoCore [goalMVar] |>.run eautoCtx)
    catch _ => pure ()

    match ← getExprMVarAssignment? goalMVar with
    | none =>
      trace[Meta.Tactic.eauto] "no proof found"
    | some proof =>
      trace[Meta.Tactic.eauto] "final proof: {← ppExpr proof}"

end Eauto

elab "eauto" : tactic =>
  Eauto.eautoMain #[] false

elab "typeclasses_eauto" : tactic =>
  Eauto.eautoMain #[] true

elab "eauto" "with" dbs:ident+ : tactic =>
  Eauto.eautoMain (dbs.map TSyntax.getId) false

elab "typeclasses_eauto" "with" dbs:ident+ : tactic =>
  Eauto.eautoMain (dbs.map TSyntax.getId) true
