
module Category.SETOID where

open import Prelude hiding (id; _∘_)
open import Category.Base
open import Logic.Equivalence
open import Logic.Setoid

open _⇒ˢ_

--- The category of setoids ---

module _ {a b} {A B : Setoid a b} where

  open Setoid hiding (≈refl; ≈sym; ≈trans)
  private module A = Setoid A
  private module B = Setoid B

  infix 4 _≈ˢ_
  record _≈ˢ_  (f g : A ⇒ˢ B) : Set (a ⊔ b) where
    field
      ≈ext : ∀ {x y} → x A.≈ y → app f x B.≈ app g y 
    infixr 30 ≈ext
    syntax ≈ext f x = f ∙≈ x

  open _≈ˢ_
  open IsEquivalence

  reflˢ : ∀ (f : A ⇒ˢ B) → f ≈ˢ f
  ≈ext (reflˢ f) = ext f

  equiv : IsEquivalence _≈ˢ_
  ≈ext (≈refl  equiv {x = f}) = ext f
  ≈ext (≈sym   equiv f=g) x=y = B.≈sym (≈ext f=g (A.≈sym x=y))
  ≈ext (≈trans equiv f=g g=h) x=y = ≈ext f=g x=y B.⟨≈⟩ ≈ext g=h A.≈refl

module _ {a b} {A B C : Setoid a b} where
  private module A = Setoid A
  private module B = Setoid B
  private module C = Setoid C

  open _≈ˢ_

  module _ {f f′ : B ⇒ˢ C} {g g′ : A ⇒ˢ B} where

    congˢ : f ≈ˢ f′ → g ≈ˢ g′ → (f ∘ˢ g) ≈ˢ (f′ ∘ˢ g′)
    ≈ext (congˢ f=f′ g=g′) x=y = ≈ext f=f′ (≈ext g=g′ x=y)

  module _ {D : Setoid a b} {f : C ⇒ˢ D} {g : B ⇒ˢ C} {h : A ⇒ˢ B} where
    private module D = Setoid D

    assocˢ : (f ∘ˢ g) ∘ˢ h ≈ˢ f ∘ˢ (g ∘ˢ h)
    ≈ext assocˢ x=y = ext f (ext g (ext h x=y))

open Cat
open _≈ˢ_

SETOID : ∀ a b → Cat (lsuc (a ⊔ b)) (a ⊔ b) (a ⊔ b)
Obj     (SETOID a b) = Setoid a b
_⇒_     (SETOID a b) A B = A ⇒ˢ B
id      (SETOID a b) = idˢ
_∘_     (SETOID a b) f g = f ∘ˢ g
_≈_     (SETOID a b) = _≈ˢ_
isEquiv (SETOID a b) = equiv
≈ext (idL   (SETOID a b) {f = f}) = ext f
≈ext (idR   (SETOID a b) {f = f}) = ext f
cong∘ (SETOID a b) = congˢ
assoc (SETOID a b) = assocˢ

--- The category of a single setoid ---

module _ {a b} (A : Setoid a b) where

  private module A = Setoid A
  open A

  SetoidCat : Cat a b lzero
  Obj SetoidCat = A.Carrier
  _⇒_ SetoidCat x y = x A.≈ y
  id SetoidCat = A.≈refl
  _∘_ SetoidCat p q = q A.⟨≈⟩ p
  Cat._≈_ SetoidCat _ _ = ⊤
  Cat.isEquiv SetoidCat = _
  idL SetoidCat = _
  idR SetoidCat = _
  cong∘ SetoidCat = _
  assoc SetoidCat = _