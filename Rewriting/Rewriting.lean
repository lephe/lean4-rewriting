abbrev relation (α: Type _) := α → α → Prop

def respectful (Rα: relation α) (Rβ: relation β): relation (α → β) :=
  fun f g => (forall a a', Rα a a' → Rβ (f a) (g a'))

def impl (P Q: Prop) := P → Q

notation Rα " ++> " Rβ => respectful Rα Rβ
notation Rα " --> " Rβ => respectful (flip Rα) Rβ
notation Rα " ==> " Rβ => respectful Rα Rβ

-- Not using Init.Core.Equivalence because it's not a typeclass

class Reflexive {α: Type _} (R: relation α) where
  refl: ∀ x, R x x

class Symmetric {α: Type _} (R: relation α) where
  symm: ∀ {x y}, R x y → R y x

class Transitive {α: Type _} (R: relation α) where
  trans: ∀ {x y z}, R x y → R y z → R x z

class PER {α: Type _} (R: relation α) extends Symmetric R, Transitive R

instance [PER R₁] [PER R₂]: PER (R₁ ==> R₂) where
  symm h x y h₁ := Symmetric.symm <| h y x <| Symmetric.symm h₁
  trans h h' x y h₁ :=
    Transitive.trans
      (h x y h₁)
      (h' y y (Transitive.trans (Symmetric.symm h₁) h₁))

class Equiv {α: Type _} (R: relation α) extends PER R, Reflexive R

instance {α}: Equiv (@Eq α) where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := Eq.trans h₁ h₂

instance: Equiv Iff where
  refl := Iff.refl
  symm := Iff.symm
  trans := Iff.trans

class Proper (R: relation α) (x: α) where
  prf: R x x

instance {R: relation α} [PER R]: Proper (R ==> R ==> Iff) R where
  prf _ _ h_a _ _ h_b :=
    ⟨fun h => Transitive.trans (Transitive.trans (Symmetric.symm h_a) h) h_b,
     fun h => Transitive.trans (Transitive.trans h_a h) (Symmetric.symm h_b)⟩

instance {R: relation α} [PER R]: Proper (R ==> Eq ==> Iff) R where
  prf a a' h_a b b' h_b :=
    ⟨by rewrite [h_b]; exact fun h => Transitive.trans (Symmetric.symm h_a) h,
     by rewrite [h_b]; exact fun h => Transitive.trans h_a h⟩

instance {R: relation α} [PER R]: Proper (Eq ==> R ==> Iff) R where
  prf a a' h_a b b' h_b :=
    ⟨by rewrite [h_a]; exact fun h => Transitive.trans h h_b,
     by rewrite [h_a]; exact fun h => Transitive.trans h (Symmetric.symm h_b)⟩

section Examples

variable (α β γ: Type)
variable (Rα: relation α) (Rβ: relation β) (Rγ: relation γ)
variable [PER Rα] [PER Rβ] [PER Rγ]
variable (Pα: α → Prop) (Pβ: β → Prop) (Pγ: γ → Prop)
variable (Pαβγ: α → β → Prop)
variable (fαβ: α → β) (fβγ: β → γ)
variable [Proper_fαβ: Proper (Rα ==> Rβ) fαβ]

example (h: Rα a a'): Rβ (fαβ a) x := by
  -- We want to rewrite `h: Rα a a'`.
  -- The TERM to rewrite is `a`. The RELATION is `Rα`.

  -- Start at the targeted occurrence of the TERM to rewrite (here `a`). Move
  -- up to the root of the term.

  -- When an application is encountered, build a `Proper` instance for it:
  -- * The argument position where the TERM to rewrite is: use the RELATION
  -- * All other arguments: use `Eq`
  -- * Output: guess it and/or see what typeclass search comes up with
  --   (here `Rβ`)
  -- Note there are many unadressed questions about how to discover the
  -- instance, including dealing with subrelations etc.
  have P₁: Proper (Rα ==> Rβ) fαβ := inferInstance
  -- Apply that instance:
  -- * For each argument left untouched, apply `_ _ rfl`
  -- * For the argument being changed, apply `_ _ h`
  have h₁: Rβ (fαβ a) (fαβ a') := P₁.prf _ _ h

  -- Then proceed upwards, replacing `h` with `h₁`, the TERM to rewrite with
  -- the call where it's located (here `fαβ a`), and the RELATION with whatever
  -- has been found (here `Rβ`).

  -- When reaching the top-level, if the goal is of sort `Prop`, finish with
  -- `Iff`, otherwise finish with `Eq`.
  have P₂: Proper (Rβ ==> Eq ==> Iff) Rβ := inferInstance
  have h₂: Iff (Rβ (fαβ a) x) (Rβ (fαβ a') x) := P₂.prf _ _ h₁ _ _ rfl

  rewrite [h₂]
  sorry
end Examples

-- Test how general we can make the typeclass search

class Subrel {α} (R₁ R₂: relation α) where
  prf: Subrelation R₁ R₂

-- These rules do blow up for obvious reasons

instance Subrel_Respectful_1 {Rα₁ Rα₂: relation α} {Rβ: relation β}
         [h_Sα: Subrel Rα₁ Rα₂] [PER Rα₁] [PER Rα₂] [PER Rβ]:
         Subrel (Rα₂ ==> Rβ) (Rα₁ ==> Rβ) where
  prf h₁ _ _ h := h₁ _ _ (h_Sα.prf h)

instance Subrel_Respectful_2 {Rα: relation α} {Rβ₁ Rβ₂: relation β}
         [PER Rα] [h_Sβ: Subrel Rβ₁ Rβ₂] [PER Rβ₁] [PER Rβ₂]:
         Subrel (Rα ==> Rβ₁) (Rα ==> Rβ₂) where
  prf h₂ _ _ h := h_Sβ.prf (h₂ _ _ h)

instance Proper_Subrel (R R': relation α) [PER R] [PER R']
   [S: Subrel R R'] [P: Proper R f]: Proper R' f where
  prf := S.prf P.prf

instance [Equiv R]: Subrel Eq R where
  prf h := match h with | .refl _ => Reflexive.refl _

instance {α} {R: relation α}: Subrel R R where
  prf h := h

section TypeclassResolution

variable (α β γ: Type)
variable (Rα₁ Rα₂: relation α) (Rβ₁ Rβ₂: relation β) (Rγ₁ Rγ₂: relation γ)
variable [Equiv Rα₁] [Equiv Rα₂] [Equiv Rβ₁] [Equiv Rβ₂] [Equiv Rγ₁] [Equiv Rγ₂]
variable (f: α → β → γ)
variable [P₁: Proper (Rα₁ ==> Rβ₁ ==> Rγ₁) f]
variable [P₂: Proper (Rα₂ ==> Rβ₂ ==> Rγ₂) f]

/- Too slow
#synth Proper (Rα₁ ==> Rβ₁ ==> Rγ₁) f
#synth Proper (Eq ==> Rβ₁ ==> Rγ₁) f
#synth Proper (Rα₁ ==> Eq ==> Rγ₁) f
#synth Proper (Eq ==> Eq ==> Rγ₁) f -/

end TypeclassResolution
