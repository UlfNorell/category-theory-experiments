
open import Category.Base

module Category.FUN {a a₁ a₂ b b₁ b₂} (C : Cat a a₁ a₂) (D : Cat b b₁ b₂) where

open import Category.Functor
open import Logic.Equivalence

open NatTrans
open Cat D
private module E = IsEquivalence

FUN : Cat _ _ _
Cat.Obj     FUN = Fun C D
Cat._⇒_     FUN = NatTrans
Cat.id      FUN = idNat
Cat._∘_     FUN = _∘Nat_
Cat._≈_     FUN α β = ∀ X → η α X ≈ η β X
E.≈refl  (Cat.isEquiv FUN)         X = ≈refl
E.≈sym   (Cat.isEquiv FUN) eq      X = ≈sym (eq X) 
E.≈trans (Cat.isEquiv FUN) eq₁ eq₂ X = ≈trans (eq₁ X) (eq₂ X)
Cat.idL     FUN α = idL
Cat.idR     FUN α = idR
Cat.cong∘   FUN eq₁ eq₂ X = cong∘ (eq₁ X) (eq₂ X)
Cat.assoc   FUN X = assoc
