
open import Category.Base

module Category.FUN {a a₁ a₂ b b₁ b₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} where

open import Category.Functor

open NatTrans
open Cat D

FUN : Cat _ _ _
FUN = record
  { Obj = Fun C D
  ; _⇒_ = NatTrans
  ; id = idNat
  ; _∘_ = _∘Nat_
  ; _≈_ = λ f g → ∀ X → η f X ≈ η g X
  ; isEquiv = record
    { ≈refl = λ _ → ≈refl
    ; ≈sym = λ eq X → ≈sym (eq X)
    ; ≈trans = λ eq eq₁ X → ≈trans (eq X) (eq₁ X) }
  ; idL = λ _ _ → idL _
  ; idR = λ _ _ → idR _
  ; cong∘ = λ f=f′ g=g′ X → cong∘ (f=f′ X) (g=g′ X)
  ; assoc = λ _ _ _ _ → assoc _ _ _
  }
