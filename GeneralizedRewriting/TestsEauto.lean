/-
# Tests for eauto
-/

import GeneralizedRewriting.Eauto
import GeneralizedRewriting.Defs

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
        (a: α) (_: P₁ a)
        (a': α) (ha'₁: P₁ a') (ha'₂: P₂ a'): β := by
  eauto

--== Typeclass resolution cases (on local context) ==--

-- Simplest grewrite case
example {α β: Type} {Rα: relation α} {Pα: α → Prop}
  (h₁: Proper (Rα ==> Iff) Pα)
  (I₁: forall {T: Type} {R: relation T}, Subrel R R)
  (I₂: Subrel Iff (flip impl))
  (goal: forall (R₁: relation (α → Prop)) (R₂: relation Prop),
     Proper R₁ Pα →
     Subrel R₁ (Rα ==> R₂) →
     Subrel R₂ (flip impl) → β): β := by
  eauto

-- Now we force the use of Subrel_respectful, which has instance arguments
example {α β: Type} {Rα: relation α} {Pα: α → Prop}
  (h₁: Proper (Rα ==> Iff) Pα)
  (I₁: Subrel Rα Rα)
  (I₂: Subrel (flip impl) (flip impl))
  (I₃: Subrel Iff (flip impl))
  (goal: forall (R₁: relation (α → Prop)) (R₂: relation Prop),
     Proper R₁ Pα →
     Subrel R₁ (Rα ==> R₂) →
     Subrel R₂ (flip impl) → β): β := by
  have h := @Subrel_respectful
  typeclasses_eauto

-- Then we start to introduce generic instances
example {α β: Type} {Rα: relation α} {Pα: α → Prop}
  (h₁: Proper (Rα ==> Iff) Pα)
  (goal: forall (R₁: relation (α → Prop)) (R₂: relation Prop),
     Proper R₁ Pα →
     Subrel R₁ (Rα ==> R₂) →
     Subrel R₂ (flip impl) → β): β := by
  have h₁ := @Subrel_respectful
  have h₂ := @Reflexive_Subrel
  have h₃ := @Reflexive.refl
  have h₄ := @Subrel_Iff_flip_impl
  typeclasses_eauto

--== Typeclass resolution cases (on database) ==--

eauto_create_db test_eauto_1
eauto_hint Subrel_respectful: test_eauto_1
eauto_hint Reflexive.refl: test_eauto_1
eauto_hint Reflexive_Subrel: test_eauto_1
eauto_hint Subrel_Iff_flip_impl: test_eauto_1
#print_eauto_db

-- Only locally-relevant hypotheses in context here
example {α β: Type} {Rα: relation α} {Pα: α → Prop}
  (h₁: Proper (Rα ==> Iff) Pα)
  (goal: forall (R₁: relation (α → Prop)) (R₂: relation Prop),
     Proper R₁ Pα →
     Subrel R₁ (Rα ==> R₂) →
     Subrel R₂ (flip impl) → β): β := by
  typeclasses_eauto with test_eauto_1

--== Using eauto as a typeclass resolution algorithm ==--

eauto_create_db test_eauto_2
eauto_hint Reflexive.refl: test_eauto_2
#print_eauto_db

example {α β: Type _} {Rα: relation α} {Pα: α → Prop}
  (h₁: Proper (Rα ==> Iff) Pα)
  (goal: forall (R₁: relation (α → Prop)) (R₂: relation Prop),
     Proper R₁ Pα →
     Subrel R₁ (Rα ==> R₂) →
     Subrel R₂ (flip impl) → β): β := by
  typeclasses_eauto with test_eauto_2
