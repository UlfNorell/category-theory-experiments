
module Category.SET where

open import Prelude
open import Category.Base
open import Logic.Equivalence

open Cat hiding (≈refl; ≈sym; ≈trans; id; _∘_)
open IsEquivalence

SET : ∀ a → Cat (lsuc a) a a
Obj (SET a)                    = Set a
_⇒_ (SET a) A B                = A → B
Cat.id (SET a)                 = id
Cat._∘_ (SET a) f g            = f ∘ g
_≈_ (SET a) f g                = ∀ {x y} → x ≡ y → f x ≡ g y
≈refl  (isEquiv (SET a))       = cong _
≈sym   (isEquiv (SET a)) f     = sym ∘ f ∘ sym
≈trans (isEquiv (SET a)) f g x = f refl ⟨≡⟩ g x
idL (SET a)                    = cong _
idR (SET a)                    = cong _
cong∘ (SET a) f g              = f ∘ g
assoc (SET a)                  = cong _
