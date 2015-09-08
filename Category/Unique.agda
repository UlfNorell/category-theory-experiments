
open import Category.Base

module Category.Unique {a b c} (C : Cat a b c) where

open import Prelude

open Cat using (Obj)

open Cat C hiding (Obj)

record ∃! {d} {X Y : Obj C} (P : (X ⇒ Y) → Set d) : Set (b ⊔ c ⊔ d) where
  field
    f    : X ⇒ Y
    sat  : P f
    uniq : ∀ (g : X ⇒ Y) → P g → g ≈ f
{-# NO_ETA ∃! #-}
