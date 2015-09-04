
open import Category.Base

module Category.Initial {a b c} (Ca : Cat a b c) where

open import Prelude
open import Category.Isomorphism

open Cat Ca

record Initial : Set (a ⊔ b ⊔ c) where
  field
    I : Obj
    ¡ : ∀ {A} → I ⇒ A
    uniq : ∀ {A} (f : I ⇒ A) → f ≈ ¡

record Terminal : Set (a ⊔ b ⊔ c) where
  field
    T : Obj
    ! : ∀ {A} → A ⇒ T
    uniq : ∀ {A} (f : A ⇒ T) → f ≈ !

initIso : (A B : Initial) → Iso Ca (Initial.I A) (Initial.I B)
initIso A B =
  record { to   = ¡A
         ; from = ¡B
         ; ida  = uniqA _ ⟨≈⟩ʳ uniqA _
         ; idb  = uniqB _ ⟨≈⟩ʳ uniqB _
         }
  where
    open Initial A renaming (I to IA; ¡ to ¡A; uniq to uniqA)
    open Initial B renaming (I to IB; ¡ to ¡B; uniq to uniqB)
