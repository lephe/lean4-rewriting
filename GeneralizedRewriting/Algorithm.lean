/-
# Generalized rewriting algorithm

This algorithm produces a "skeleton" of the proof for a rewrite. It provides
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

## Skeleton algorithm

At the top level:
  (u, R, p) ← solve t
  add_to_ψ (Γ ⊢ Subrel R (flip impl))
  return (u, R, p, ψ)

On input t:

  1. [UNIFY]
     If t unifies with the lhs of ρ, yielding ψ and [ρ' : R t u]:
       return (u, R, ρ')

  2. [APP]
     If t is an app [f e] and the whnf of the type of f in [Γ ∪ ψ] is
     some non-dependent function type [τ → σ]:
       (f', F, pf) ← solve f
       (e', E, pe) ← solve e
       add_to_ψ {Γ ⊢ ?T : relation σ}
       add_to_ψ {Γ ⊢ ?sub : Subrel F (E ++> ?T)}
       return (f' e', ?T, ?sub f f' pf e e' pe)

  3. [ARROW]
     If t is a non-dependent arrow [τ₁ → τ₂].
       (u, S, p) ← solve (impl τ₁ τ₂)
       match u with
       | impl τ₁' τ₂' => return (τ₁' → τ₂', S, p)
       | _ => ???

  4. [LAMBDA]
     TODO

  5. [PI]
     TODO

  6. [ATOM]
     If all else fails and there is no occurrence of the lhs of ρ in t:
       τ ← type t
       add_to_ψ {Γ ⊢ ?S : relation τ}
       add_to_ψ {Γ ⊢ Proper ?S t}
       return (t, ?S, ?m)
-/

import GeneralizedRewriting.Defs
import Lean

open Lean Meta Elab Tactic

initialize
  registerTraceClass `Meta.Tactic.grewrite

-- Environment where the skeleton algorithm is run

structure RewriteState where
  ρ: Expr
  ρ_R: Expr
  ρ_t: Expr
  ρ_u: Expr
  ψ: Array Expr

abbrev RewriteM := StateT RewriteState TacticM

namespace RewriteM

def run: RewriteM α → RewriteState → TacticM (α × RewriteState) :=
  StateT.run

def addConstraint (e: Expr): RewriteM Unit := do
  let st ← get
  set { st with ψ := st.ψ.push e }

def skeleton (t: Expr): RewriteM (Expr × Expr × Expr) :=
  withTraceNode `Meta.Tactic.grewrite (fun _ => return m!"skeleton: {t}") do
  let state ← get

  -- [UNIFY]: First try to unify t with the LHS of ρ to apply ρ directly
  if ← isDefEq t state.ρ_t then
    trace[Meta.Tactic.grewrite] "using rule: UNIFY"
    return (state.ρ_u, state.ρ_R, state.ρ)

  -- [APP]: Handle applications
  if let .app f e := t then
    let type_f ← whnf (← inferType f)
    trace[Meta.Tactic.grewrite] "type_f = {type_f}"
    if let some (_, σ) := type_f.arrow? then
        trace[Meta.Tactic.grewrite] "using rule: APP"
        let (f', F, pf) ← skeleton f
        let (e', E, pe) ← skeleton e
        let m_T ← mkFreshExprMVar (← mkAppM ``relation #[σ])
        let m_sub ← mkFreshExprMVar (← mkAppM ``Subrel #[F, ← mkAppM ``respectful #[E, m_T]])
        addConstraint m_T
        addConstraint m_sub
        return (mkApp f' e', m_T, mkAppN m_sub #[f, f', pf, e, e', pe])

  -- [ATOM]: Default to requiring proper on the atom
  trace[Meta.Tactic.grewrite] "using rule: ATOM"
  let τ ← inferType t
  let m_S ← mkFreshExprMVar (← mkAppM ``relation #[τ])
  let m_Proper ← mkFreshExprMVar (← mkAppM ``Proper #[m_S, t])
  addConstraint m_S
  addConstraint m_Proper
  return (t, m_S, m_Proper)

def skeletonMain (t: Expr): RewriteM (Expr × Expr × Expr) := do
  let (u, R, p) ← skeleton t
  let MainSubrel ← mkAppM ``Subrel #[R, ← mkAppM ``flip #[mkConst ``impl]]
  let m_MainSubrel ← mkFreshExprMVar MainSubrel
  addConstraint m_MainSubrel
  return (u, R, p)

end RewriteM


-- Tactic front-end

elab "grewrite " h:term : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let goalDecl ← goal.getDecl
    let h ← elabTerm h .none
    let ρ ← inferType (← whnf h)

    match ρ with
    | .app (.app ρ_R ρ_t) ρ_u =>
        trace[Meta.Tactic.grewrite] "The goal is: {goalDecl.type}"
        trace[Meta.Tactic.grewrite]
          "Found relation: ρ_R={ρ_R} ρ_t={ρ_t} ρ_u={ρ_u}"
        let st: RewriteState := { ρ, ρ_R, ρ_t, ρ_u, ψ := #[] }
        let ((u, R, p), st') ← RewriteM.skeletonMain goalDecl.type st |>.run
        let ψ := st'.ψ

        let pp ← ψ.mapM fun e => do
          let type_e ← inferType e
          return f!"\n  {e}: {← ppExpr type_e}"
        trace[Meta.Tactic.grewrite] "Constraints to solve: {Format.join pp.toList}"
        -- TODO: solve st'.ψ and apply p
    | _ =>
        throwError f!"Could not interpret [{ρ}] as a relation"
        return
    return
