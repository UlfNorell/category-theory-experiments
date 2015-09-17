
module Category.Universal where

open import Prelude hiding (_∘_; map)
open import Category.Base
open import Category.Functor
open import Category.Comma
open import Category.Initial
import Category.Unique as Uniq

open Cat using (Obj)
open Fun

module _ {a a₁ a₂ b b₁ b₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} where

  InitialMorphism : Obj C → Fun D C → Set _
  InitialMorphism X U = Initial (Const₁ X ↓ U)

  TerminalMorphism : Fun D C → Obj C → Set _
  TerminalMorphism U X = Terminal (U ↓ Const₁ X)

  --- Equivalent formulations ---

  open Cat C hiding (Obj)
  open Cat D using () renaming (_⇒_ to _⇒D_; _≈_ to _≈D_)

  open Uniq D

  record InitialMorphism′ (X : Obj C) (U : Fun D C) : Set (a₁ ⊔ a₂ ⊔ b ⊔ b₁ ⊔ b₂) where
    field
      A : Obj D
      ϕ : X ⇒ Map U A
      prop : (Y : Obj D) (f : X ⇒ Map U Y) →
             ∃! λ (g : A ⇒D Y) → map U g ∘ ϕ ≈ f
  {-# NO_ETA InitialMorphism′ #-}

  module _ {X U} (m : InitialMorphism X U) where

    open Initial _ m using (I; uniqArrow)
    open module U {X} = Uniq.∃! _ (uniqArrow {X}) using () renaming (f to IArr; uniq to iUniq)
    open CommaObj _ _ I using (β; f)
    open module Bang X = CommaMorph _ _ (IArr {X}) using () renaming (h to !; homomorphic to hom)

    private
     module M (Y : Obj D) (g : X ⇒ Map U Y) where
      Z : CommaObj (Const₁ X) U
      CommaObj.α Z = _
      CommaObj.β Z = Y
      CommaObj.f Z = g

      α : (h : β ⇒D Y) → map U h ∘ f ≈ g → CommaMorph (Const₁ X) U I Z
      CommaMorph.g (α _ _) = tt
      CommaMorph.h (α h _) = h
      CommaMorph.homomorphic (α h eq) = idR _ ⟨≈⟩ʳ eq

      uniq : ∃! λ h → map U h ∘ f ≈ g
      Uniq.∃!.f    uniq = ! Z
      Uniq.∃!.sat  uniq = hom Z ʳ⟨≈⟩ idR _
      Uniq.∃!.uniq uniq h eq = snd (iUniq (α h eq) _)

    open M
    open InitialMorphism′
    oneWay : InitialMorphism′ X U
    A    oneWay = β
    ϕ    oneWay = f
    prop oneWay = uniq
