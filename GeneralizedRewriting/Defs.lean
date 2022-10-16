/-
## Relation classes

Init.Core provides some utilities, specifically `Init.Core.Equivalence`, but
we're not using it because it's not a typeclass (and difficult to relate to the
other relation classes).
-/

import GeneralizedRewriting.Eauto

abbrev relation (α: Type _) := α → α → Prop

class Reflexive {α: Type _} (R: relation α) where
  refl: ∀ x, R x x

class Symmetric {α: Type _} (R: relation α) where
  symm: ∀ {x y}, R x y → R y x

class Transitive {α: Type _} (R: relation α) where
  trans: ∀ {x y z}, R x y → R y z → R x z

class PER {α: Type _} (R: relation α) extends Symmetric R, Transitive R

class Equiv {α: Type _} (R: relation α) extends PER R, Reflexive R

eauto_hint Reflexive.refl: grewrite

/-
## Morphisms
-/

def respectful (Rα: relation α) (Rβ: relation β): relation (α → β) :=
  fun f g => forall a a', Rα a a' → Rβ (f a) (g a')

def pointwise_relation (α: Type _) {β} (R: relation β) : relation (α -> β) :=
  fun f g => forall a, R (f a) (g a)

def forall_relation {α: Type _} {P: α → Type _}
    (sig: forall a, relation (P a)): relation (forall x, P x) :=
  fun f g => forall a, sig a (f a) (g a)

def impl (P Q: Prop) := P → Q

class Proper (R: relation α) (x: α): Prop where
  prf: R x x

class Subrel {α} (R₁ R₂: relation α): Prop where
  prf: Subrelation R₁ R₂

notation Rα " ++> " Rβ => respectful Rα Rβ
notation Rα " --> " Rβ => respectful (flip Rα) Rβ
notation Rα " ==> " Rβ => respectful Rα Rβ

-- Instances used by the search algorithm

instance Reflexive_Subrel: Reflexive (@Subrel α) where
  refl _ := ⟨id⟩

instance Subrel_respectful [Sα: @Subrel α R₂ R₁] [Sβ: @Subrel β S₁ S₂]:
    Subrel (R₁ ==> S₁) (R₂ ==> S₂) where
  prf H _ _ h := Sβ.prf (H _ _ (Sα.prf h))

instance Proper_pointwise_relation {α β: Type _}:
    Proper (Subrel ==> Subrel) (@pointwise_relation α β) where
  prf _ _ h := ⟨fun hpr a => h.prf (hpr a)⟩

instance Subrel_pointwise [S: @Subrel β R₁ R₂]:
    Subrel (pointwise_relation α R₁) (pointwise_relation α R₂) where
  prf h a := S.prf (h a)

-- Standard instances

instance: Equiv (@Eq α) where
  refl  := Eq.refl
  symm  := Eq.symm
  trans := Eq.trans

instance: Equiv Iff where
  refl  := Iff.refl
  symm  := Iff.symm
  trans := Iff.trans

instance Proper_flip [P: Proper (Rα ==> Rβ ==> Rγ) f]:
    Proper (Rβ ==> Rα ==> Rγ) (flip f) where
  prf _ _ h_b _ _ h_a := P.prf _ _ h_a _ _ h_b

instance Subrel_Eq [Reflexive R]: Subrel Eq R where
  prf h := h ▸ Reflexive.refl _

instance respectful_PER [PER R₁] [PER R₂]: PER (R₁ ==> R₂) where
  symm h x y h₁ := Symmetric.symm <| h y x <| Symmetric.symm h₁
  trans h h' x y h₁ :=
    Transitive.trans
      (h x y h₁)
      (h' y y (Transitive.trans (Symmetric.symm h₁) h₁))

instance Subrel_Iff_impl: Subrel Iff impl where
  prf h := h.1

instance Subrel_Iff_flip_impl: Subrel Iff (flip impl) where
  prf h := h.2

--

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
