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
TODO: Cancel metavars' assignments if applying a given hint fails to close
TODO: Recurse in the search and bound it
-/

import Lean.Meta.SynthInstance
import Lean.Util.Trace
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Apply

open Lean Meta Elab Tactic

initialize
  registerTraceClass `Meta.Tactic.eauto
  registerTraceClass `Meta.Tactic.eauto.goals
  registerTraceClass `Meta.Tactic.eauto.hints

namespace Eauto

inductive Hint where
  | Constant (n: Name) (expr: Expr) (type: Expr)
  | Extern (term: Term) (tactic: TSyntax `tactic) (cost: Nat)

instance: ToString Hint where
  toString := fun
    | .Constant n _ type => s!"{n}: {type}"
    | .Extern term tactic cost => s!"Extern {cost}: {term} => {tactic}"

def Hint.toString (h: Hint): MetaM Format := do
  match h with
  | .Constant n _ type => return f!"{n}: {← ppExpr type}"
  | .Extern term tactic cost => return f!"Extern {cost}: {term} => {tactic}"

structure HintDB where
  name: Name
  hints: List Hint

structure Context where
  hintDatabases: List HintDB
  useTypeclasses: Bool
  maximumDepth: Nat

abbrev EautoM := ReaderT Context TacticM

/- Returns a proof of `goal`; updates metavariables as a side-effect. -/
def solveSubgoal (goalMvar: MVarId) (depth: Nat): EautoM (Option Expr) :=
    withTraceNode `Meta.Tactic.eauto
    (fun _ => return m!"goal[{depth}]: {← Meta.ppExpr (← goalMvar.getDecl).type}") do

  let goal := (← goalMvar.getDecl).type

  trace[Meta.Tactic.eauto.goals] "goal[{depth}]: {← ppExpr goal}"

  if depth > (← read).maximumDepth then
    return .none

  for db in (← read).hintDatabases do
    for hint in db.hints do
--      trace[Meta.Tactic.eauto] "[{db.name}] {← hint.toString}"
      -- TODO: How to cancel the metavariable update resulting from `isDefEq`
      -- if subgoal resolution fails?
      match hint with
      | .Constant _ expr type =>
          if ← isDefEq goal type then
            trace[Meta.Tactic.eauto.hints] "[{db.name}] trying hint: {← hint.toString}"
            -- TODO: Can this application fail?
            let subgoals ← goalMvar.apply expr
            trace[Meta.Tactic.eauto.hints] "subgoals: {subgoals}"
      | _ =>
          continue

  return .none

end Eauto

-- Tactic front-end for testing

def eautoMain (useTypeclasses: Bool): TacticM Unit :=
  Elab.Tactic.withMainContext do
    let goalMvar ← Elab.Tactic.getMainGoal

    -- Load hypotheses as hints
    let ctx ← Lean.MonadLCtx.getLCtx
    let hypHints ← ctx.foldrM (fun (decl: LocalDecl) (hyps: List Eauto.Hint) => do
        if decl.isAuxDecl then
          return hyps
        else
          return .Constant decl.userName decl.toExpr (← inferType decl.toExpr) :: hyps)
      []
    let hypDB: Eauto.HintDB := {
      name := `_localcontext,
      hints := hypHints
    }

    let eautoCtx: Eauto.Context := {
      hintDatabases := [hypDB],
      useTypeclasses := useTypeclasses,
      maximumDepth := 5,
    }

    -- Solve a single goal
    let result ← Eauto.solveSubgoal goalMvar 0 eautoCtx
    match result with
    | .none => trace[Meta.Tactic.eauto] "no proof found"
    | .some r => trace[Meta.Tactic.eauto] "final proof: {← ppExpr r}"

elab "eauto" : tactic =>
  eautoMain false

elab "typeclasses_eauto" : tactic =>
  eautoMain true
