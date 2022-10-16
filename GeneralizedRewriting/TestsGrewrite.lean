import GeneralizedRewriting.Algorithm
import GeneralizedRewriting.Eauto

section Examples

-- TODO: Fails when (α β γ: Type) because the hint `Reflexive.refl` has a
-- universe parameter which is not properly instantiated by `eauto`
variable (α β γ: Type _)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ==> Rβ) fαβ]
variable [Proper_Rα: Proper (Rα ==> Iff) Pα]

set_option trace.Meta.Tactic.grewrite true
set_option trace.Meta.Tactic.eauto true
set_option trace.Meta.Tactic.eauto.hints true

example (h: Rα a a') : Pα a := by
  -- TODO: Why does the following `have` confuse the skeleton algorithm?
  -- have h₁ := @Reflexive.refl
  grewrite h
  sorry

example (h: Rα a a') : Rα a x := by
  grewrite h
  sorry

example (h: Rα a a') : Rβ (fαβ a) x := by
  grewrite h
  sorry

end Examples
