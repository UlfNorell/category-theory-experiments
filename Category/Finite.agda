
module Category.Finite where

open import Prelude hiding (id; _∘_)
open import Category.Base

open Cat

Zero : Cat lzero lzero lzero
Obj     Zero = ⊥
_⇒_     Zero ()
id      Zero {}
_∘_     Zero {}
_≈_     Zero {}
isEquiv Zero {}
idL     Zero {}
idR     Zero {}
cong∘   Zero {}
assoc   Zero {}

One : Cat lzero lzero lzero
Obj     One = ⊤
_⇒_     One _ _ = ⊤
id      One = _
_∘_     One = _
_≈_     One _ _ = ⊤
isEquiv One = record{}
idL     One = _
idR     One = _
cong∘   One = _
assoc   One = _
