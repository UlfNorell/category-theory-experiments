
module Category.Limit where

open import Prelude hiding (_∘_; map)
open import Category.Base
open import Category.Functor
open import Category.FUN
open import Category.Universal
open import Category.Comma
open import Category.Initial

open Cat using (Obj)
open Fun
open NatTrans

module _ {a b c} (J : Cat a b c) {a₁ b₁ c₁} (C : Cat a₁ b₁ c₁) where

  Diagram : Set _
  Diagram = Fun J C

  DIAG = FUN J C

module _ {a b c} {J : Cat a b c} {a₁ b₁ c₁} {C : Cat a₁ b₁ c₁} where

  open Cat using (Obj)
  open Cat C hiding (Obj)
  open Cat J using () renaming (_⇒_ to _⇒J_)
  open Fun
  open NatTrans

  Δ : Fun C (FUN J C)
  Map Δ N                = Const N
  η (map Δ f) _          = f
  naturality (map Δ f) _ = idLR
  cong-map Δ eq _        = eq
  resp-id  Δ _           = ≈refl
  resp-∘   Δ f g _       = ≈refl

  Cone : (N : Obj C) (F : Diagram J C) → Set (a ⊔ b ⊔ b₁ ⊔ c₁)
  Cone N F = NatTrans (Map Δ N) F

  Co-cone : (N : Obj C) (F : Diagram J C) → Set (a ⊔ b ⊔ b₁ ⊔ c₁)
  Co-cone N F = NatTrans F (Map Δ N)

  Limit : (F : Diagram J C) → Set _
  Limit F = TerminalMorphism Δ F

  Colimit : (F : Diagram J C) → Set _
  Colimit F = InitialMorphism F Δ

  -- Limits are cones
  module _ {F : Diagram J C} (Lim : Limit F) where

    open module T = Terminal _ Lim using (T; !; uniq)
    open module O = CommaObj _ _ T using () renaming (f to α; α to L′)
    open module M {X} = CommaMorph _ _ (! {X}) using () renaming (g to !g; h to !h; homomorphic to hom)

    L : Obj C
    L = L′

    limitCone : Cone L F
    limitCone = α