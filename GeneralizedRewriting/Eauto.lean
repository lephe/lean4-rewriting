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

open Lean Meta Elab Tactic

initialize
  registerTraceClass `Meta.Tactic.eauto
  registerTraceClass `Meta.Tactic.eauto.goals
  registerTraceClass `Meta.Tactic.eauto.hints

initialize eautoFailedExceptionId : InternalExceptionId ← registerInternalExceptionId `eautoFailed

namespace Eauto

inductive Hint where
  | Constant (n: Name) (expr: Expr) (type: Expr)
  | Extern (term: Term) (tactic: TSyntax `tactic) (cost: Nat)

instance : ToMessageData Hint where
  toMessageData
    | .Constant n _ type => m!"{n}: {type}"
    | .Extern term tactic cost => m!"Extern {cost}: {term} => {tactic}"

structure HintDB where
  name: Name
  hints: Array Hint

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

mutual
partial def solve (goalMVar: MVarId) (depth: Nat) (goalStack: List (Nat × MVarId)):
    EautoM Unit := do
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
            let subgoals ← goalMVar.apply ldecl.toExpr
            trace[Meta.Tactic.eauto.hints] "applying hypothesis: {ldecl.userName}: {← ppExpr t}"
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
                let subgoals ← goalMVar.apply expr
                trace[Meta.Tactic.eauto.hints] "[{db.name}] applying hint: {hint}"
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

end Eauto

-- Tactic front-end for testing

def eautoMain (useTypeclasses: Bool): TacticM Unit :=
  withMainContext do
    let goalMVar ← getMainGoal

    let eautoCtx: Eauto.Context := {
      hintDatabases := #[]
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


elab "eauto" : tactic =>
  eautoMain false

elab "typeclasses_eauto" : tactic =>
  eautoMain true
