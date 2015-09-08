
module Category.Finite where

open import Prelude
open import Category.Base

Zero : Cat lzero lzero lzero
Zero = record
  { Obj     = ⊥
  ; _⇒_     = λ ()
  ; id      = λ {}
  ; _∘_     = λ {}
  ; _≈_     = λ {}
  ; isEquiv = λ {}
  ; idL     = λ {}
  ; idR     = λ {}
  ; cong∘   = λ {}
  ; assoc   = λ {}
  }

One : Cat lzero lzero lzero
One = record
  { Obj = ⊤
  ; _⇒_ = λ _ _ → ⊤
  ; _≈_ = λ _ _ → ⊤
  ; isEquiv = record {}
  }
