
module Category.CAT where

open import Prelude hiding (id; _∘_; map)
open import Category.Base
open import Category.Functor
open import Category.Isomorphism

open NatTrans
open NatIso
open Fun

private
  module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} {E : Cat c c₁ c₂}
           {F F′ : Fun D E} {G G′ : Fun C D} where
    open Cat E
    lift○ : NatTrans F F′ → NatTrans G G′ → NatTrans (F ○ G) (F′ ○ G′)
    lift○ f g = record
      { η = λ _ → map F′ (η g _) ∘ η f _
      ; naturality = λ h →
        assoc _ _ _ ʳ⟨≈⟩
        cong∘L (resp-∘ F′ _ _ ʳ⟨≈⟩ cong-map F′ (naturality g h)) ⟨≈⟩
        naturality f _ ⟨≈⟩
        cong∘R (resp-∘ F _ _) ⟨≈⟩
        assoc _ _ _ ʳ⟨≈⟩ʳ
        cong∘L (naturality f _)
      }

    id○ : ∀ {X} (F=F′ : F ≋ F′) (G=G′ : G ≋ G′) →
          (map F (η (from G=G′) X) ∘ η (from F=F′) (Map G′ X)) ∘
          (map F′ (η (to G=G′) X) ∘ η (to F=F′) (Map G X)) ≈ id
    id○ F=F′ G=G′ =
      cong∘L (naturality (from F=F′) _) ⟨≈⟩
      assoc _ _ _ ⟨≈⟩
      cong∘R (assoc _ _ _ ʳ⟨≈⟩
              cong∘L (resp-∘ F′ _ _ ʳ⟨≈⟩
                      cong-map F′ (idF G=G′ _) ⟨≈⟩
                      resp-id F′) ⟨≈⟩
              idL _) ⟨≈⟩
      idF F=F′ _

private
 module _ {a a₁ a₂ b b₁ b₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} (F : Fun A B) where

  open Cat B hiding (Obj)

  IdL : Id ○ F ≋ F
  η          (to IdL)   _ = id
  naturality (to IdL)   _ = idRL
  η          (from IdL) _ = id
  naturality (from IdL) _ = idRL
  idF  IdL X = idL _
  idG  IdL X = idL _

  IdR : F ○ Id ≋ F
  η          (to IdR)   _ = id
  naturality (to IdR)   _ = idRL
  η          (from IdR) _ = id
  naturality (from IdR) _ = idRL
  idF  IdR X = idL _
  idG  IdR X = idL _

private
 module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} {C : Cat c c₁ c₂} where

   module _ {d d₁ d₂} {D : Cat d d₁ d₂} where

     open Cat D

     Assoc : (F : Fun C D) (G : Fun B C) (H : Fun A B) → F ○ G ○ H ≋ F ○ (G ○ H)
     η          (to (Assoc F G H)) X = id
     naturality (to (Assoc F G H)) f = idRL
     η          (from (Assoc F G H)) X = id
     naturality (from (Assoc F G H)) f = idRL
     idF  (Assoc F G H) X = idL _
     idG  (Assoc F G H) X = idL _

   open Cat C

   Cong : {F F′ : Fun B C} {G G′ : Fun A B} → F ≋ F′ → G ≋ G′ → F ○ G ≋ F′ ○ G′
   to   (Cong eqF eqG) = lift○ (to eqF) (to eqG)
   from (Cong eqF eqG) = lift○ (from eqF) (from eqG)
   idF  (Cong eqF eqG) X = id○ eqF eqG
   idG  (Cong eqF eqG) X = id○ (≋sym eqF) (≋sym eqG)


open Cat
CAT : ∀ a b c → Cat _ _ _
Obj (CAT a b c)     = Cat a b c
_⇒_ (CAT a b c)     = Fun
id (CAT a b c)      = Id
_∘_ (CAT a b c)     = _○_
_≈_ (CAT a b c)     = _≋_
isEquiv (CAT a b c) = ≋Equiv
idL (CAT a b c)     = IdL
idR (CAT a b c)     = IdR
cong∘ (CAT a b c)   = Cong
assoc (CAT a b c)   = Assoc
