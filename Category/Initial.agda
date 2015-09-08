
module Category.Initial where

open import Prelude
open import Category.Base
open import Category.Isomorphism
import Category.Unique as Uniq

module _ {a b c} (Ca : Cat a b c) where

  open Cat Ca
  open Uniq Ca

  record Initial : Set (a ⊔ b ⊔ c) where
    field
      I : Obj
      uniqArrow : ∀ {A} → ∃! λ (f : I ⇒ A) → ⊤

    open module EU {A} = ∃! (uniqArrow {A}) using () renaming (f to ¡) public
    uniq : ∀ {A} (f : I ⇒ A) → f ≈ ¡
    uniq f = ∃!.uniq uniqArrow f _

  {-# NO_ETA Initial #-}

  record Terminal : Set (a ⊔ b ⊔ c) where
    field
      T : Obj
      ! : ∀ {A} → A ⇒ T
      uniq : ∀ {A} (f : A ⇒ T) → f ≈ !

-- Some proofs
module _ {a b c} {Ca : Cat a b c} where

  open Cat Ca

  initIso : (A B : Initial Ca) → Iso Ca (Initial.I A) (Initial.I B)
  initIso A B =
    record { to   = ¡A
           ; from = ¡B
           ; ida  = uniqA _ ⟨≈⟩ʳ uniqA _
           ; idb  = uniqB _ ⟨≈⟩ʳ uniqB _
           }
    where
      open Initial Ca A renaming (I to IA; ¡ to ¡A; uniq to uniqA)
      open Initial Ca B renaming (I to IB; ¡ to ¡B; uniq to uniqB)
