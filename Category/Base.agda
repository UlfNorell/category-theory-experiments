
module Category.Base where

open import Prelude hiding (id; _∘_)
open import Logic.Equivalence

record Cat a b c : Set (lsuc (a ⊔ b ⊔ c)) where
  infix 4 _≈_
  infixl 9 _∘_
  field
    Obj  : Set a
    _⇒_ : Obj → Obj → Set b
    id   : ∀ {A} → A ⇒ A
    _∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    _≈_     : ∀ {A B} → (A ⇒ B) → (A ⇒ B) → Set c
    isEquiv : ∀ {A B} → IsEquivalence (_≈_ {A} {B})
    idL     : ∀ {A B} (f : A ⇒ B) → id ∘ f ≈ f
    idR     : ∀ {A B} (f : A ⇒ B) → f ∘ id ≈ f
    cong∘   : ∀ {X Y Z} {f f′ : Y ⇒ Z} {g g′ : X ⇒ Y} → f ≈ f′ → g ≈ g′ → f ∘ g ≈ f′ ∘ g′
    assoc   : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B) →
              (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

  private module E {A} {B} = IsEquivalence (isEquiv {A} {B})
  open E public

  idLR : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f ∘ id
  idLR = idL _ ⟨≈⟩ʳ idR _

  idRL : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ id ∘ f
  idRL = ≈sym idLR

  cong∘L : ∀ {X Y Z} {f f′ : Y ⇒ Z} {g : X ⇒ Y} → f ≈ f′ → f ∘ g ≈ f′ ∘ g
  cong∘L eq = cong∘ eq ≈refl

  cong∘R   : ∀ {X Y Z} {f : Y ⇒ Z} {g g′ : X ⇒ Y} → g ≈ g′ → f ∘ g ≈ f ∘ g′
  cong∘R = cong∘ ≈refl

{-# NO_ETA Cat #-}

--- The dual category ---

_op : ∀ {a b c} → Cat a b c → Cat a b c
C op = record
  { Obj  = Obj
  ; _⇒_ = flip _⇒_
  ; id   = id
  ; _∘_ = flip _∘_
  ; _≈_    = _≈_
  ; isEquiv = isEquiv
  ; idL     = idR
  ; idR     = idL
  ; cong∘   = flip cong∘
  ; assoc   = λ f g h → ≈sym (assoc h g f)
  }
  where open Cat C
