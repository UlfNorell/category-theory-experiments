
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
    private module C = Cat C
    private module D = Cat D
    open Cat E
    lift○ : NatTrans F F′ → NatTrans G G′ → NatTrans (F ○ G) (F′ ○ G′)
    η       (lift○ f g) X = map F′ (η g X) ∘ η f (Map G X)
    natural (lift○ f g) h =
      assoc ʳ⟨≈⟩ cong∘L (resp-∘ F′ _ _ ʳ⟨≈⟩ cong-map F′ (natural g h)) ⟨≈⟩
      natural f _ ⟨≈⟩ cong∘R (resp-∘ F _ _) ⟨≈⟩ʳ cong∘L (natural f _) ⟨≈⟩
      assoc

    id○ : ∀ {X} (F=F′ : F ≋ F′) (G=G′ : G ≋ G′) →
          (map F (η (from G=G′) X) ∘ η (from F=F′) (Map G′ X)) ∘
          (map F′ (η (to G=G′) X) ∘ η (to F=F′) (Map G X)) ≈ id
    id○ F=F′ G=G′ =
      cong∘L (natural (from F=F′) _) ⟨≈⟩
      assoc ⟨≈⟩
      cong∘R (assoc ʳ⟨≈⟩
              cong∘L (resp-∘ F′ _ _ ʳ⟨≈⟩
                      cong-map F′ (idF G=G′) ⟨≈⟩
                      resp-id F′) ⟨≈⟩
              idL) ⟨≈⟩
      idF F=F′

private
 module _ {a a₁ a₂ b b₁ b₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} {F : Fun A B} where

  open Cat B hiding (Obj)

  IdL : Id ○ F ≋ F
  η       (to IdL)   _ = id
  natural (to IdL)   _ = idRL
  η       (from IdL) _ = id
  natural (from IdL) _ = idRL
  idF  IdL = idL
  idG  IdL = idL

  IdR : F ○ Id ≋ F
  η       (to IdR)   _ = id
  natural (to IdR)   _ = idRL
  η       (from IdR) _ = id
  natural (from IdR) _ = idRL
  idF  IdR = idL
  idG  IdR = idL

private
 module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} {C : Cat c c₁ c₂} where

   module _ {d d₁ d₂} {D : Cat d d₁ d₂} where

     open Cat D

     Assoc : {F : Fun C D} {G : Fun B C} {H : Fun A B} → F ○ G ○ H ≋ F ○ (G ○ H)
     η       (to Assoc) X = id
     natural (to Assoc) f = idRL
     η       (from Assoc) X = id
     natural (from Assoc) f = idRL
     idF  Assoc = idL
     idG  Assoc = idL

   open Cat C

   Cong : {F F′ : Fun B C} {G G′ : Fun A B} → F ≋ F′ → G ≋ G′ → F ○ G ≋ F′ ○ G′
   to   (Cong eqF eqG) = lift○ (to eqF) (to eqG)
   from (Cong eqF eqG) = lift○ (from eqF) (from eqG)
   idF  (Cong eqF eqG) = id○ eqF eqG
   idG  (Cong eqF eqG) = id○ (≋sym eqF) (≋sym eqG)


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
