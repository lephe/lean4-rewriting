/-
# Generalized rewriting algorithm

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

## Inputs and outputs

Inputs:
  τ  -- Input term
  ρ  -- Rewriting lemma (of the form `∀ ϕ…, R α… t u`)
Outputs:
  τ' -- Rewritten term
  R  -- Relation for rewriting (contains metavariables)
  p  -- Proof of rewrite
  ψ  -- Typeclass queries that need solving

TODO:
  - What kind of new constraints ψ do you get from unifying in the UNIFY rule?
    ---> I'll assume these are metavariable assignments happening in MetaM
  - Can the rewrite of [impl τ₁ τ₂] in ARROW not return an impl?
  - What if there is a unification in ATOM? What is the default?
-/

import GeneralizedRewriting.Defs
import GeneralizedRewriting.Eauto
import Lean

open Lean Meta Elab Tactic

initialize
  registerTraceClass `Meta.Tactic.grewrite

-- Environment where the outline algorithm is run

structure RewriteState where
  ρ: Expr
  ρ_R: Expr
  ρ_t: Expr
  ρ_u: Expr
  ρ_proof: Expr
  ψ: Array Expr

abbrev RewriteM := StateT RewriteState TacticM

namespace RewriteM

def run: RewriteM α → RewriteState → TacticM (α × RewriteState) :=
  StateT.run

def addConstraint (e: Expr): RewriteM Unit := do
  let st ← get
  set { st with ψ := st.ψ.push e }

partial def outline (t: Expr): RewriteM (Expr × Expr × Expr) := do
  let t ← whnf t
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"outline: {t}") do
  let state ← get

  -- [UNIFY]: If t unifies with the LHS of ρ then we have an occurrence, and we
  -- can apply ρ directly.
  if ← isDefEq t state.ρ_t then
    trace[Meta.Tactic.grewrite] "using rule: UNIFY"
    return (state.ρ_u, state.ρ_R, state.ρ_proof)

  -- [APP]: If t is an app `f e` where f is of non-dependent function type
  -- `τ → σ`, guess a relation `?m_T: relation σ` for the co-domain. This is
  -- also the place where we allow `Subrel` instances.
  if let .app f e := t then
    let type_f ← whnf (← inferType f)
    if let some (_, σ) := type_f.arrow? then
        trace[Meta.Tactic.grewrite] "using rule: APP (function type: {type_f})"
        let (f', F, pf) ← outline f
        let (e', E, pe) ← outline e
        let m_T ← mkFreshExprMVar (← mkAppM ``relation #[σ])
        let m_sub ← mkFreshExprMVar (← mkAppM ``Subrel #[F, ← mkAppM ``respectful #[E, m_T]])
        addConstraint m_sub
        return (mkApp f' e', m_T,
                ← mkAppOptM ``Subrel.prf #[none, none, none, m_sub, f, f', pf, e, e', pe])

  -- TODO: [ARROW], [LAMBDA] and [FORALL]

  -- [ATOM]: Default to requiring `Proper` on the atom for a suitable relation
  trace[Meta.Tactic.grewrite] "using rule: ATOM ({← whnf t})"
  let τ ← inferType t
  let m_S ← mkFreshExprMVar (← mkAppM ``relation #[τ])
  let m_Proper ← mkFreshExprMVar (← mkAppM ``Proper #[m_S, t])
  addConstraint m_Proper
  return (t, m_S, ← mkAppOptM ``Proper.prf #[none, none, none, m_Proper])

def outlineMain (t: Expr): RewriteM (Expr × Expr × Expr) := do
  -- At the top-level, we need to rewrite for any relation which is a
  -- subrelation of `flip impl`.
  -- TODO: To rewrite in a hypothesis, use a subrelation of `impl`.
  let (u, R, p) ← outline t
  let MainSubrel ← mkAppM ``Subrel #[R, ← mkAppM ``flip #[mkConst ``impl]]
  let m_sub ← mkFreshExprMVar MainSubrel
  addConstraint m_sub
  return (u, R, ← mkAppOptM ``Subrel.prf #[none, none, none, m_sub, none, none, p])

end RewriteM


-- Tactic front-end

elab "grewrite " h:term : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let h ← elabTerm h .none
    let ρ ← inferType (← whnf h)

    match ρ with
    | .app (.app ρ_R ρ_t) ρ_u =>
        let st: RewriteState := { ρ, ρ_R, ρ_t, ρ_u, ρ_proof := h, ψ := #[] }
        let ((_, _, p), st') ← RewriteM.outlineMain goalType st |>.run
        let ψ := st'.ψ

        let pp ← ψ.mapM fun e => do
          let type_e ← inferType e
          return f!"\n  {← ppExpr type_e}"
        trace[Meta.Tactic.grewrite] "constraints to solve: {Format.join pp.toList}"

        -- Try to solve the constraints with `eauto`
        let success ← Eauto.eautoMain (ψ.map Expr.mvarId!).toList #[`grewrite] true
        if !success then
          throwError "grewrite: unable to solve constraints"

        let subgoals ← goal.apply (← instantiateMVars p)
        replaceMainGoal subgoals
    | _ =>
        throwError f!"unable to interpret {ρ} as a relation"
        return
    return
