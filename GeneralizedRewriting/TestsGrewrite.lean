import GeneralizedRewriting.Algorithm
import GeneralizedRewriting.Eauto

section Examples

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ==> Rβ) fαβ]
variable [Proper_Pα: Proper (Rα ==> Iff) Pα]
variable [PER Rα] [PER Rβ]

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true

-- Smallest example
example (h: Rα a a') (finish: Pα a') : Pα a := by
  grewrite h
  exact finish

-- Rewrite a PER within itself
example (h: Rα a a') (finish: Rα a' x) : Rα a x := by
  grewrite h
  exact finish
example (h: Rα a a') (finish: Rα x a') : Rα x a := by
  grewrite h
  exact finish

-- Nested function call
example (h: Rα a a') (finish: Rβ (fαβ a') x): Rβ (fαβ a) x := by
  grewrite h
  exact finish

-- Multiple occurrences
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite h
  exact finish
example (h: Rα a a') (finish: Rα a' a): Rα a a := by
  grewrite h at 1
  exact finish
example (h: Rα a a') (finish: Rα a a'): Rα a a := by
  grewrite h at 2
  exact finish
example (h: Rα a a') (finish: Rα a' a'): Rα a a := by
  grewrite h at -1
  grewrite h at 1
  exact finish

-- More complex selection
example (h: Rα a a') (finish: Pα a'): Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a ∧ Pα a := by
  grewrite h at 5
  grewrite h at - 2 4
  grewrite h
  repeat (constructor; assumption)
  assumption

end Examples
