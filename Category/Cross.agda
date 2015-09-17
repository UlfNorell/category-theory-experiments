
module Category.Cross where

open import Prelude hiding (id; _∘_; map)
open import Category.Base
open import Category.Functor
open import Logic.Equivalence

module _ {a a₁ a₂ b b₁ b₂} (A : Cat a a₁ a₂) (B : Cat b b₁ b₂) where

  open Cat
  private module A = Cat A
  private module B = Cat B

  private module E = IsEquivalence

  infix 4 _[×]_
  _[×]_ : Cat (a ⊔ b) (a₁ ⊔ b₁) (a₂ ⊔ b₂)
  Obj _[×]_ = Obj A × Obj B
  _⇒_ _[×]_ X Y = fst X A.⇒ fst Y × snd X B.⇒ snd Y
  Cat.id _[×]_ = A.id , B.id
  Cat._∘_ _[×]_ f g = fst f A.∘ fst g , snd f B.∘ snd g
  _≈_ _[×]_ f g = fst f A.≈ fst g × snd f B.≈ snd g
  E.≈refl  (isEquiv _[×]_) = ≈refl A , ≈refl B
  E.≈sym   (isEquiv _[×]_) x=y = ≈sym A (fst x=y) , ≈sym B (snd x=y)
  E.≈trans (isEquiv _[×]_) x=y y=z = ≈trans A (fst x=y) (fst y=z) , ≈trans B (snd x=y) (snd y=z)
  idL _[×]_ = A.idL , B.idL
  idR _[×]_ = A.idR , B.idR
  cong∘ _[×]_ f=f′ g=g′ = A.cong∘ (fst f=f′) (fst g=g′) , B.cong∘ (snd f=f′) (snd g=g′)
  assoc _[×]_ = A.assoc , B.assoc

module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂ d d₁ d₂} {A : Cat a a₁ a₂}  {B : Cat b b₁ b₂} {C : Cat c c₁ c₂} {D : Cat d d₁ d₂} where

  open Fun
  _×F_ : (F : Fun A B) (G : Fun C D) → Fun (_[×]_ A C) (_[×]_ B D)
  Map (F ×F G) X = Map F (fst X) , Map G (snd X)
  map (F ×F G) f = map F (fst f) , map G (snd f)
  cong-map (F ×F G) (f , g) = cong-map F f , cong-map G g
  resp-id (F ×F G) = resp-id F , resp-id G
  resp-∘ (F ×F G) f g = resp-∘ F (fst f) (fst g) , resp-∘ G (snd f) (snd g)