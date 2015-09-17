
module Logic.Equivalence where

open import Agda.Primitive

record IsEquivalence {a b} {A : Set a} (_≈_ : A → A → Set b) : Set (a ⊔ b) where
  field
    ≈refl  : ∀ {x} → x ≈ x
    ≈sym   : ∀ {x y} → x ≈ y → y ≈ x
    ≈trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

  infixr 0 ≈trans _⟨≈⟩ʳ_ _ʳ⟨≈⟩_ _ʳ⟨≈⟩ʳ_
  syntax ≈trans a b = a ⟨≈⟩ b

  _⟨≈⟩ʳ_ : ∀ {x y z : A} → x ≈ y → z ≈ y → x ≈ z
  x=y ⟨≈⟩ʳ z=y = x=y ⟨≈⟩ ≈sym z=y

  _ʳ⟨≈⟩_ : ∀ {x y z : A} → y ≈ x → y ≈ z → x ≈ z
  y=x ʳ⟨≈⟩ y=z = ≈sym y=x ⟨≈⟩ y=z

  _ʳ⟨≈⟩ʳ_ : ∀ {x y z : A} → y ≈ x → z ≈ y → x ≈ z
  y=x ʳ⟨≈⟩ʳ z=y = ≈sym y=x ⟨≈⟩ ≈sym z=y

-- {-# NO_ETA IsEquivalence #-}