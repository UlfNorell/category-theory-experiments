
module Category.SET where

open import Prelude
open import Category.Base

SET : ∀ a → Cat (lsuc a) a a
SET a = record
  { Obj = Set a
  ; _⇒_ = λ A B → A → B
  ; id = id
  ; _∘_ = λ f g → f ∘ g
  ; _≈_ = λ f g → ∀ {x y} → x ≡ y → f x ≡ g y
  ; isEquiv = record
    { ≈refl = cong _
    ; ≈sym  = λ f → sym ∘ f ∘ sym
    ; ≈trans = λ f g x → f refl ⟨≡⟩ g x
    }
  ; idL   = λ _ → cong _
  ; idR   = λ _ → cong _
  ; cong∘ = λ f g → f ∘ g
  ; assoc = λ _ _ _ → cong _
  }
