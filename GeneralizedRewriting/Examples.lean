import GeneralizedRewriting.Algorithm

section Examples

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ==> Rβ) fαβ]

set_option trace.Meta.Tactic.grewrite true

example (h: Rα a a') : Pα a := by
  grewrite h
  sorry

example (h: Rα a a') : Rα a x := by
  grewrite h
  sorry

example (h: Rα a a') : Rβ (fαβ a) x := by
  grewrite h
  sorry
end Examples
