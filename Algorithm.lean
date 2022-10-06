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