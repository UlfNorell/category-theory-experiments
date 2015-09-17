
module Category.Base where

open import Prelude hiding (id; _∘_)
open import Logic.Equivalence
open import Logic.Setoid

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
    idL     : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f
    idR     : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ f
    cong∘   : ∀ {X Y Z} {f f′ : Y ⇒ Z} {g g′ : X ⇒ Y} → f ≈ f′ → g ≈ g′ → f ∘ g ≈ f′ ∘ g′
    assoc   : ∀ {A B C D} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
              (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)

  infixl 9 cong∘
  syntax cong∘ f g = f ∘≈ g

  private module E {A} {B} = IsEquivalence (isEquiv {A} {B})
  open E public

  Hom : Obj → Obj → Setoid b c
  Setoid.Carrier (Hom X Y) = X ⇒ Y
  Setoid._≈_    (Hom X Y) = _≈_
  Setoid.isEquiv (Hom X Y) = isEquiv

  idLR : ∀ {A B} {f : A ⇒ B} → id ∘ f ≈ f ∘ id
  idLR = idL ⟨≈⟩ʳ idR

  idRL : ∀ {A B} {f : A ⇒ B} → f ∘ id ≈ id ∘ f
  idRL = ≈sym idLR

  cong∘L : ∀ {X Y Z} {f f′ : Y ⇒ Z} {g : X ⇒ Y} → f ≈ f′ → f ∘ g ≈ f′ ∘ g
  cong∘L eq = cong∘ eq ≈refl

  cong∘R   : ∀ {X Y Z} {f : Y ⇒ Z} {g g′ : X ⇒ Y} → g ≈ g′ → f ∘ g ≈ f ∘ g′
  cong∘R = cong∘ ≈refl

{-# NO_ETA Cat #-}

--- The dual category ---

open Cat
_op : ∀ {a b c} → Cat a b c → Cat a b c
Obj  (C op) = Obj C
_⇒_ (C op) = flip (_⇒_ C) 
id (C op) = id C
_∘_ (C op) = flip (_∘_ C)
_≈_ (C op) = _≈_ C
isEquiv (C op) = isEquiv C
idL (C op) = idR C
idR (C op) = idL C
cong∘ (C op) = flip (cong∘ C)
assoc (C op) = ≈sym C (assoc C)
