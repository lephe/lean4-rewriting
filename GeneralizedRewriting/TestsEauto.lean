/-
# Tests for eauto
-/

import GeneralizedRewriting.Eauto
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true

--== Basic computational examples ==--

-- Assumption
example: P → P := by
  eauto

-- Function application with no intermediate variable
example: (P → Q → R → S) → R → Q → P → S := by
  eauto

-- Reverse application
example: (((P → Q) → R) → S) → (Q → R) → P → S := by
  eauto

-- Intermediate metavariable for ?a:α
example (Pα: α → Prop) (f: forall a, Pα a → β) (a: α) (ha: Pα a): β := by
  eauto

-- Backtracking example; using ha₁ first which is incorrect
example (P₁ P₂: α → Prop) (f: forall (a: α), P₁ a → P₂ a → β)
        (a: α) (ha₁: P₁ a)
        (a': α) (ha'₁: P₁ a') (ha'₂: P₂ a'): β := by
  eauto
