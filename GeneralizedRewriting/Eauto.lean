/-
# Basic typeclass inference with backtracking

This file implements a very rough imitation of Coq's `eauto`. It is used to
share a set of goals (here: typeclass queries) that may share metavariables,
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
  depth : Nat

abbrev EautoM := ReaderT Context MetaM

instance : MonadBacktrack Meta.SavedState EautoM where
  saveState := Meta.saveState
  restoreState s := s.restore

partial def solveSubgoal (goalMVar: MVarId) : EautoM Unit := do
  let ctx ← read
  let depth := ctx.depth
  withTraceNode `Meta.Tactic.eauto
    (fun _ => return m!"goal[{depth}]: {← goalMVar.getType}") do

  let goal ← goalMVar.getType

  trace[Meta.Tactic.eauto.goals] "goal[{depth}]: {goal}"

  if depth > ctx.maximumDepth then
    return

  for db in ctx.hintDatabases do
    for hint in db.hints do
      try
        commitIfNoEx do
    --      trace[Meta.Tactic.eauto] "[{db.name}] {← hint.toString}"
          match hint with
          | .Constant _ expr _ =>
              trace[Meta.Tactic.eauto.hints] "[{db.name}] trying hint: {hint}"
              let subgoals ← goalMVar.apply expr
              trace[Meta.Tactic.eauto.hints] "subgoals: {subgoals}"
              withReader (λ ctx => { ctx with depth := depth + 1 }) do
                subgoals.forM solveSubgoal
          | _ => pure ()
        catch _ => pure ()

end Eauto

-- Tactic front-end for testing

def eautoMain (useTypeclasses: Bool): TacticM Unit :=
  withMainContext do
    let goalMVar ← getMainGoal

    -- Load hypotheses as hints
    let mut hypHints := #[]
    for ldecl in ← getLCtx do
      if ! ldecl.isAuxDecl then
        hypHints := hypHints.push $
          .Constant ldecl.userName ldecl.toExpr (← inferType ldecl.toExpr)

    let hypDB: Eauto.HintDB := {
      name := `_localcontext,
      hints := hypHints
    }

    let eautoCtx: Eauto.Context := {
      hintDatabases := #[hypDB]
      useTypeclasses := useTypeclasses
      maximumDepth := 5
      depth := 0
    }

    -- Solve a single goal
    Eauto.solveSubgoal goalMVar |>.run eautoCtx
    match ← getExprMVarAssignment? goalMVar with
    | none =>
      trace[Meta.Tactic.eauto] "no proof found"
    | some proof =>
      trace[Meta.Tactic.eauto] "final proof: {← instantiateMVars proof}"


elab "eauto" : tactic =>
  eautoMain false

elab "typeclasses_eauto" : tactic =>
  eautoMain true
