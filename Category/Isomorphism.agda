
open import Category.Base

module Category.Isomorphism {a b c} (C : Cat a b c) where

open import Agda.Primitive
open Cat C

record Iso (A B : Obj) : Set (b ⊔ c) where
  field
    to   : A ⇒ B
    from : B ⇒ A
    ida  : from ∘ to ≈ id
    idb  : to ∘ from ≈ id
