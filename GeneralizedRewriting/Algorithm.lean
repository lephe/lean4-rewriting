/-
## Inputs and outputs

Context:
  Γ  -- Environment [ro]
  ρ  -- Rewriting lemma (of the form ∀ ϕ→, R α→ t u) [ro]
  ψ  -- Output constraints (Propers and subrelations mainly) [rw]
Inputs:
  τ  -- Input term
Outputs:
  τ' -- Rewritten term
  R  -- Relation for rewriting (contains metavariables)
  p  -- Proof of rewrite

TODO:
  - What kind of new constraints ψ do you get from unifying in the UNIFY rule?
    ---> I'll assume these are metavariable assignments happening in MetaM
  - Can the rewrite of [impl τ₁ τ₂] in ARROW not return an impl?
  - What if there is a unification in ATOM? What is the default?

## Skeleton algorithm

Start:
  (u, R, p) ← solve t
  add_to_ψ (get_Γ ⊢ subrelation R impl⁻¹)
  return (u, R, p, get_ψ)

On input t:

  1. [UNIFY]
     If t unifies with the lhs of ρ, yielding ψ and [ρ' : R t u]:

     return (u, R, ρ')

  2. [APP]
     If t is an app [f e] and the whnf of the type of f in [get_Γ ∪ get_ψ] is
     some non-dependent function type [τ → σ]:

     (f', F, pf) ← solve f
     (e', E, pe) ← solve e
     ?T ← make_meta_variable in environment get_Γ
     add_to_ψ {get_Γ ⊢ ?T : relation σ}
     ?sub ← make_meta_variable in environment get_Γ
     add_to_ψ {get_Γ ⊢ ?sub : subrelation F (E ++> ?T)}
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
     ?S ← make_meta_variable in environment get_Γ
     add_to_ψ {get_Γ ⊢ ?S : relation τ}
     ?m ← make_meta_variable in environment get_Γ
     add_to_ψ {get_Γ ⊢ Proper ?S t}
     return (t, ?S, ?m)

## Assumptions

The set of instances of `subrelation` should be:
  - Transitive
  - Closed under `pointwise_relation`
otherwise we might miss some valid solutions.
-/

import GeneralizedRewriting.Defs
import Lean.Meta
import Lean.Meta.InferType
import Lean.Elab.Term
import Lean.Util.Trace

open Lean Meta Elab Tactic

initialize
  registerTraceClass `Meta.Tactic.grewrite

-- Environment where the skeleton algorithm is run

structure RewriteState where
  ρ: Expr
  ρ_R: Expr
  ρ_t: Expr
  ρ_u: Expr
  ψ: List Expr

abbrev RewriteM := StateT RewriteState TacticM

namespace RewriteM

def run: RewriteM α → RewriteState → TacticM (α × RewriteState) :=
  StateT.run

def addConstraint (e: Expr): RewriteM Unit := do
  let st ← get
  set { st with ψ := st.ψ ++ [e] }

def skeleton (t: Expr): RewriteM (Expr × Expr × Expr) := traceCtx `Meta.Tactic.grewrite do
  let state ← get

  trace[Meta.Tactic.grewrite] "skeleton: {← ppExpr t}"

  -- [UNIFY]: First try to unify t with the LHS of ρ to apply ρ directly
  if ← isDefEq t state.ρ_t then
    trace[Meta.Tactic.grewrite] "using rule: UNIFY"
    return (state.ρ_u, state.ρ_R, state.ρ)

  -- [APP]: Handle applications
  if let .app f e _ := t then
    let type_f ← whnf (← inferType f)
    trace[Meta.Tactic.grewrite] "type_f = {← ppExpr type_f}"
    if type_f.isArrow then
        trace[Meta.Tactic.grewrite] "using rule: APP"
        let σ := match type_f with
                 | .forallE _ _ σ _ => σ
                 | _ => type_f /- impossible -/
        let (f', F, pf) ← skeleton f
        let (e', E, pe) ← skeleton e
        let m_T ← mkFreshExprMVar (← mkAppM ``relation #[σ])
        let m_sub ← mkFreshExprMVar (← mkAppM ``Subrel #[F,
          ← mkAppM ``respectful #[E, m_T]])
        addConstraint m_T
        addConstraint m_sub
        return (mkApp f' e', m_T, mkAppN m_sub #[f, f', pf, e, e', pe])

  -- [ATOM]: Default to requiring proper on the atom
  trace[Meta.Tactic.grewrite] "using rule: ATOM"
  let τ ← inferType t
  let m_S ← mkFreshExprMVar (← mkAppM ``relation #[τ]) (userName := `S)
  let m_Proper ← mkFreshExprMVar (← mkAppM ``Proper #[m_S, t]) (userName := `m)
  addConstraint m_S
  addConstraint m_Proper
  return (t, m_S, m_Proper)

def skeletonMain (t: Expr): RewriteM (Expr × Expr × Expr) := do
  let (u, R, p) ← skeleton t
  addConstraint (← mkAppM ``Subrel #[R, ← mkAppM ``flip #[mkConst ``impl]])
  return (u, R, p)

end RewriteM

-- Tactic front-end

elab "grewrite " h:term : tactic =>
  Elab.Tactic.withMainContext do
    let goal ← Elab.Tactic.getMainGoal
    let goalDecl ← Meta.getMVarDecl goal
    let h ← Elab.Term.elabTerm h .none
    let ρ ← Meta.inferType (← Meta.whnf h)

    match ρ with
    | .app (.app ρ_R ρ_t _) ρ_u _ =>
        trace[Meta.Tactic.grewrite] "The goal is: {← Meta.ppExpr goalDecl.type}"
        trace[Meta.Tactic.grewrite] "Found relation: ρ_R={← Meta.ppExpr ρ_R} ρ_t={← Meta.ppExpr ρ_t} ρ_u={← Meta.ppExpr ρ_u}"
        let st: RewriteState := { ρ, ρ_R, ρ_t, ρ_u, ψ := [] }
        let ((u, R, p), st') ← RewriteM.run (RewriteM.skeletonMain goalDecl.type) st
        let ψ := st'.ψ
        let pp ← ψ.mapM (fun e => ppExpr e)
        trace[Meta.Tactic.grewrite] "Constraints to solve: {pp}"
        -- TODO: solve st'.ψ and apply p
    | _ =>
        throwError f!"Could not interpret [{← Meta.ppExpr ρ}] as a relation"
        return
    return
