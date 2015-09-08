
module Category.Comma where

open import Prelude hiding (id; _∘_; map)
open import Category.Base
open import Category.Functor
open import Logic.Equivalence

open Cat using (Obj)
open Fun

module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} {C : Cat c c₁ c₂} where

  module E = IsEquivalence

  open Cat A using () renaming (_⇒_ to _⇒A_; id to idA; _∘_ to _∘A_; _≈_ to _≈A_)
  open Cat B using () renaming (_⇒_ to _⇒B_; id to idB; _∘_ to _∘B_; _≈_ to _≈B_)

  open Cat C hiding (Obj)

  module _ (S : Fun A C) (T : Fun B C) where

    -- CommaObj : Set _
    -- CommaObj = Σ (Obj A) λ α → Σ (Obj B) λ β → Map S α ⇒ Map T β
    record CommaObj : Set (a ⊔ b ⊔ c₁) where
      field
        α : Obj A
        β : Obj B
        f : Map S α ⇒ Map T β
    {-# NO_ETA CommaObj #-}

    record CommaMorph (X Y : CommaObj) : Set (a₁ ⊔ b₁ ⊔ c₂) where
      open CommaObj
      field
        g : α X ⇒A α Y
        h : β X ⇒B β Y
        homomorphic : f Y ∘ map S g ≈ map T h ∘ f X
    {-# NO_ETA CommaMorph #-}

    open CommaMorph
    open CommaObj
    _↓_ : Cat _ _ _
    Obj _↓_ = CommaObj
    Cat._⇒_ _↓_ = CommaMorph
    CommaMorph.g (Cat.id _↓_) = idA
    CommaMorph.h (Cat.id _↓_) = idB
    CommaMorph.homomorphic (Cat.id _↓_) = cong∘R (resp-id S) ⟨≈⟩ idR _ ⟨≈⟩ʳ
                                          cong∘L (resp-id T) ⟨≈⟩ idL _
    g (Cat._∘_ _↓_ i j) = g i ∘A g j
    h (Cat._∘_ _↓_ i j) = h i ∘B h j
    homomorphic (Cat._∘_ _↓_ i j) =
      cong∘R (resp-∘ S _ _) ⟨≈⟩
      assoc _ _ _ ʳ⟨≈⟩
      cong∘L (homomorphic i) ⟨≈⟩
      assoc _ _ _ ⟨≈⟩
      cong∘R (homomorphic j) ⟨≈⟩
      assoc _ _ _ ʳ⟨≈⟩ʳ
      cong∘L (resp-∘ T _ _)
    Cat._≈_ _↓_ i j = g i ≈A g j × h i ≈B h j
    E.≈refl  (Cat.isEquiv _↓_) = Cat.≈refl A , Cat.≈refl B
    E.≈sym   (Cat.isEquiv _↓_) = Cat.≈sym A *** Cat.≈sym B
    E.≈trans (Cat.isEquiv _↓_) eq = Cat.≈trans A (fst eq) *** Cat.≈trans B (snd eq)
    Cat.idL _↓_ _ = Cat.idL A _ , Cat.idL B _
    Cat.idR _↓_ _ = Cat.idR A _ , Cat.idR B _
    Cat.cong∘ _↓_ eq = Cat.cong∘ A (fst eq) *** Cat.cong∘ B (snd eq)
    Cat.assoc _↓_ _ _ _ = Cat.assoc A _ _ _ , Cat.assoc B _ _ _

module _ {a a₁ a₂} {A : Cat a a₁ a₂} (X : Obj A) where

  Slice : Cat _ _ _
  Slice = Id {C = A} ↓ Const₁ X

  Coslice : Cat _ _ _
  Coslice = Const₁ X ↓ Id {C = A}
