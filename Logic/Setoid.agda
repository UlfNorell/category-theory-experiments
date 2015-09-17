
module Logic.Setoid where

open import Prelude
open import Logic.Equivalence

record Setoid a b : Set (lsuc (a ⊔ b)) where
  field
    Carrier : Set a
    _≈_    : Carrier → Carrier → Set b
    isEquiv : IsEquivalence _≈_
  open IsEquivalence isEquiv public

record _⇒ˢ_ {a a₁ b b₁} (A : Setoid a a₁) (B : Setoid b b₁) : Set (a ⊔ a₁ ⊔ b ⊔ b₁) where
  open Setoid
  open Setoid A using () renaming (_≈_ to _≈A_)
  open Setoid B using () renaming (_≈_ to _≈B_)
  field
    app : Carrier A → Carrier B
    ext : ∀ {x y} → x ≈A y → app x ≈B app y
  infixr 30 app ext
  syntax app f g = f ∙ g
  syntax ext f g = f ⊜ g
{-# NO_ETA _⇒ˢ_ #-}

open _⇒ˢ_

idˢ : ∀ {a a₁} {A : Setoid a a₁} → A ⇒ˢ A
app idˢ x = x
ext idˢ x = x

infixl 9 _∘ˢ_
_∘ˢ_ : ∀ {a a₁ b b₁ c c₁} {A : Setoid a a₁} {B : Setoid b b₁} {C : Setoid c c₁} →
         (B ⇒ˢ C) → (A ⇒ˢ B) → (A ⇒ˢ C)
app (f ∘ˢ g) = app f ∘ app g
ext (f ∘ˢ g) = ext f ∘ ext g
