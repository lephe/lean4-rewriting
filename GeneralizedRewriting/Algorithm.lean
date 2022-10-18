/-
# Generalized rewriting
-/

import GeneralizedRewriting.Defs
import GeneralizedRewriting.Eauto
import Lean

open Lean Meta Elab Tactic

/-
## Outline algorithm

This algorithm produces a "outline" of the proof for a rewrite. It provides
the main structure, but leaves two elements undefined (through metavariables):

1. Which relations to use in the codomain of relevant function calls;
2. Which subrelation instances to use.

It produces a set of typeclass queries for `Proper` and `Subrel` which
reference subterms of the goal as well as newly-introduced metavariables for
relations to guess.

Note that `Subrel` could in principle be used everywhere, which makes it rather
difficult to deal with. The algorithm makes simplifications by assuming that
the set of instances of `Subrel` is:

- Transitive;
- Closed under `pointwise_relation`,

in order to generate a workable set of queries. If the set of instances of
`Subrel` does not satisfy the following requirements, the rewriting tactic may
fail to generate a proof that the rewrite is correct.

Based on:
[1] Sozeau, M. 2009. A New Look at Generalized Rewriting in Type Theory.
    Journal of Formalized Reasoning. 2, 1 (Jan. 2009), 41–62.
    DOI:https://doi.org/10.6092/issn.1972-5787/1574.
-/

initialize
  registerTraceClass `Meta.Tactic.grewrite

inductive SelectionCriterion where
  | Only (occs: Array Nat)
  | AllBut (occs: Array Nat)

def SelectionCriterion.selects: SelectionCriterion → Nat → Bool
  | Only occs => occs.contains
  | AllBut occs => not ∘ occs.contains

-- Environment where the outline algorithm is run

structure RewriteState where
  -- Rewrite to apply: ρ ≡ ρ_R ρ_t ρ_u
  ρ: Expr
  ρ_R: Expr
  ρ_t: Expr
  ρ_u: Expr
  -- Proof of ρ
  ρ_proof: Expr
  -- Number of occurrences found so far, and selected
  occsFound: Nat
  occsSelected: Nat
  -- Selection criterion
  selection: SelectionCriterion

abbrev RewriteM := StateT RewriteState TacticM

/-
Inputs:
  t -- Input term
  ρ -- Rewriting lemma (of the form `∀ ϕ…, R α… t u`) (in `RewriteState`)
Outputs:
  u -- Rewritten term
  R -- Relation for rewriting (contains metavariables)
  p -- Proof of rewrite
  ψ -- Typeclass queries that need solving
  N -- Number of occurences of the rewrite found in `t` (in `RewriteState`)
-/
partial def outline (t: Expr): RewriteM (Expr × Expr × Expr × Array Expr) := do
  let t ← whnf t
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"outline: {t}") do
  let state ← get

  -- [UNIFY]: If t unifies with the LHS of ρ then we have an occurrence, and we
  -- can apply ρ directly.
  if ← isDefEq t state.ρ_t then
    trace[Meta.Tactic.grewrite] "using rule: UNIFY"
    let Nf := state.occsFound
    let Ns := state.occsSelected
    -- Occurrences are numbered starting at 1.
    let selected := state.selection.selects (Nf+1)
    set { state with occsFound := Nf + 1, occsSelected := Ns + (if selected then 1 else 0) }
    if selected then
      return (state.ρ_u, state.ρ_R, state.ρ_proof, #[])

  -- [APP]: If t is an app `f e` where f is of non-dependent function type
  -- `τ → σ`, guess a relation `?m_T: relation σ` for the co-domain. This is
  -- also the place where we allow `Subrel` instances.
  if let .app f e := t then
    let type_f ← whnf (← inferType f)
    if let some (_, σ) := type_f.arrow? then
        trace[Meta.Tactic.grewrite] "using rule: APP (function type: {type_f})"
        let (f', F, pf, ψf) ← outline f
        let (e', E, pe, ψe) ← outline e
        let m_T ← mkFreshExprMVar (← mkAppM ``relation #[σ])
        let m_sub ← mkFreshExprMVar (← mkAppM ``Subrel #[F, ← mkAppM ``respectful #[E, m_T]])
        let p ← mkAppOptM ``Subrel.prf #[none, none, none, m_sub, f, f', pf, e, e', pe]
        -- Very important order of constraints: first the argument, then the
        -- function, once the relation on the argument has been guessed
        return (mkApp f' e', m_T, p, (ψe ++ ψf).push m_sub)

  -- TODO: [ARROW], [LAMBDA] and [FORALL]
  -- TODO: Can the rewrite of [impl τ₁ τ₂] in ARROW not return an impl?

  -- [ATOM]: Default to requiring `Proper` on the atom for a suitable relation
  trace[Meta.Tactic.grewrite] "using rule: ATOM ({← whnf t})"
  let τ ← inferType t
  let m_S ← mkFreshExprMVar (← mkAppM ``relation #[τ])
  let m_Proper ← mkFreshExprMVar (← mkAppM ``Proper #[m_S, t])
  let p ← mkAppOptM ``Proper.prf #[none, none, none, m_Proper]
  return (t, m_S, p, #[m_Proper])

def outlineMain (t: Expr): RewriteM (Expr × Expr × Expr × Array Expr) := do
  -- At the top-level, we need to rewrite for any relation which is a
  -- subrelation of `flip impl`.
  -- TODO: To rewrite in a hypothesis, use a subrelation of `impl`.
  let (u, R, p, ψ) ← outline t
  let MainSubrel ← mkAppM ``Subrel #[R, ← mkAppM ``flip #[mkConst ``impl]]
  let m_sub ← mkFreshExprMVar MainSubrel
  let p' ← mkAppOptM ``Subrel.prf #[none, none, none, m_sub, none, none, p]
  return (u, R, p', ψ.push m_sub)

def grewrite (h: Expr) (occs: SelectionCriterion): TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let ρ ← inferType (← whnf h)

    match ρ with
    | .app (.app ρ_R ρ_t) ρ_u =>
        let st: RewriteState := {
          ρ, ρ_R, ρ_t, ρ_u,
          ρ_proof := h,
          occsFound := 0,
          occsSelected := 0,
          selection := occs }
        let ((_, _, p, ψ), st') ← outlineMain goalType st |>.run
        let Ns := st'.occsSelected

        trace[Meta.Tactic.grewrite] "{st'.occsFound} occurrences found, {Ns} selected"
        if Ns = 0 then
          throwError "grewrite: no occurrence found or none selected"

        let pp ← ψ.mapM fun e => do return f!"\n{← ppExpr (← inferType e)}"
        trace[Meta.Tactic.grewrite] "constraints to solve: {Format.join pp.toList}"

        -- Try to solve the constraints with `typeclasses_eauto with grewrite`
        let success ← Eauto.eautoMain (ψ.map Expr.mvarId!).toList #[`grewrite] true
        if !success then
          throwError "grewrite: unable to solve constraints"

        let subgoals ← goal.apply (← instantiateMVars p)
        replaceMainGoal subgoals
    | _ =>
        throwError f!"unable to interpret {ρ} as a relation"
        return
    return

-- Tactic front-end

elab "grewrite " h:term : tactic => do
  let h ← elabTerm h .none
  grewrite h (.AllBut #[])

elab "grewrite " h:term " at " neg:"-"? occs:num+ : tactic => do
  let h ← elabTerm h .none
  let occs := occs.map TSyntax.getNat
  let selection: SelectionCriterion :=
    match neg with
    | none => .Only occs
    | _ => .AllBut occs
  grewrite h selection
