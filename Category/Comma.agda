
module Category.Comma where

open import Prelude hiding (id; _∘_; map)
open import Category.Base
open import Category.Functor

module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} {C : Cat c c₁ c₂} where

  open Cat using (Obj)
  open Fun

  open Cat A using () renaming (_⇒_ to _⇒A_; id to idA; _∘_ to _∘A_; _≈_ to _≈A_)
  open Cat B using () renaming (_⇒_ to _⇒B_; id to idB; _∘_ to _∘B_; _≈_ to _≈B_)

  open Cat C hiding (Obj)

  module _ (S : Fun A C) (T : Fun B C) where

    record CommaObj : Set (a ⊔ b ⊔ c₁) where
      field
        α : Obj A
        β : Obj B
        f : Map S α ⇒ Map T β

    record CommaMorph (X Y : CommaObj) : Set (a₁ ⊔ b₁ ⊔ c₂) where
      open CommaObj
      field
        g : α X ⇒A α Y
        h : β X ⇒B β Y
        homomorphic : f Y ∘ map S g ≈ map T h ∘ f X

    _↓_ : Cat _ _ _
    _↓_ = record
      { Obj = CommaObj
      ; _⇒_ = CommaMorph
      ; id = record { g = idA ; h = idB
                    ; homomorphic = cong∘R (resp-id S) ⟨≈⟩ idR _ ⟨≈⟩ʳ
                                    cong∘L (resp-id T) ⟨≈⟩ idL _ }
      ; _∘_ = λ f f′ →
        let open CommaMorph f
            open CommaMorph f′ renaming (g to g′; h to h′; homomorphic to homomorphic′)
        in record
        { g = g ∘A g′
        ; h = h ∘B h′
        ; homomorphic =
            cong∘R (resp-∘ S _ _) ⟨≈⟩
            assoc _ _ _ ʳ⟨≈⟩
            cong∘L homomorphic ⟨≈⟩
            assoc _ _ _ ⟨≈⟩
            cong∘R homomorphic′ ⟨≈⟩
            assoc _ _ _ ʳ⟨≈⟩ʳ
            cong∘L (resp-∘ T _ _) }
      ; _≈_ = λ f f′ → CommaMorph.g f ≈A CommaMorph.g f′ × CommaMorph.h f ≈B CommaMorph.h f′
      ; isEquiv = record
        { ≈refl = Cat.≈refl A , Cat.≈refl B
        ; ≈sym = Cat.≈sym A *** Cat.≈sym B
        ; ≈trans = λ eq → Cat.≈trans A (fst eq) *** Cat.≈trans B (snd eq) }
      ; idL = λ f → Cat.idL A _ , Cat.idL B _
      ; idR = λ f → Cat.idR A _ , Cat.idR B _
      ; cong∘ = λ f=f′ g=g′ → Cat.cong∘ A (fst f=f′) (fst g=g′) , Cat.cong∘ B (snd f=f′) (snd g=g′) 
      ; assoc = λ _ _ _ → Cat.assoc A _ _ _ , Cat.assoc B _ _ _
      }
