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

-- Avoid a `Reflexive (@Subrel α)` instance because that would allow `Subrel`
-- to be guessed as a codomain relation without an explicit hint, which almost
-- never makes sense.
theorem Reflexive_Subrel (R: relation α): Subrel R R := ⟨id⟩

instance Subrel_respectful [Sα: @Subrel α R₂ R₁] [Sβ: @Subrel β S₁ S₂]:
    Subrel (R₁ ==> S₁) (R₂ ==> S₂) where
  prf H _ _ h := Sβ.prf (H _ _ (Sα.prf h))

instance Subrel_pointwise [S: @Subrel β R₁ R₂]:
    Subrel (pointwise_relation α R₁) (pointwise_relation α R₂) where
  prf h a := S.prf (h a)

instance Proper_pointwise_relation {α β: Type _}:
    Proper (Subrel ==> Subrel) (@pointwise_relation α β) where
  prf _ _ h := ⟨fun hpr a => h.prf (hpr a)⟩

instance Proper_Reflexive {α: Type _} (Rα: relation α) [Reflexive Rα] (a: α):
    Proper Rα a where
  prf := Reflexive.refl _

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

-- TODO: We can assume `Transitive R` and instead put `flip` in judicious
-- places for these rules. (This might require better suport for `flip`.)

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

-- Order the hints by most specific first
eauto_create_db grewrite
eauto_hint Reflexive_Subrel: grewrite
eauto_hint Reflexive.refl: grewrite
