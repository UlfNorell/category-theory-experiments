
module Category.Functor where

open import Prelude hiding (id; _∘_; map)
open import Logic.Equivalence
open import Category.Base
open import Category.Isomorphism

record Fun {a₁ a₂ a₃ b₁ b₂ b₃} (C : Cat a₁ a₂ a₃) (D : Cat b₁ b₂ b₃) : Set (a₁ ⊔ a₂ ⊔ a₃ ⊔ b₁ ⊔ b₂ ⊔ b₃) where
  open Cat hiding (_≈_)
  open Cat D using (_≈_)
  private
    _⇒C_ = _⇒_ C
    _⇒D_ = _⇒_ D
    idC  = id C
    idD  = id D
    _∘C_ = _∘_ C
    _∘D_ = _∘_ D
    _≈C_ = Cat._≈_ C
  field
    Map     : Obj C → Obj D
    map     : ∀ {X Y : Obj C} → (X ⇒C Y) → (Map X ⇒D Map Y)
    cong-map : ∀ {X Y : Obj C} {f g : X ⇒C Y} → f ≈C g →  map f ≈ map g
    resp-id : ∀ {X : Obj C} → map (idC {X}) ≈ idD
    resp-∘  : ∀ {X Y Z : Obj C} (f : Y ⇒C Z) (g : X ⇒C Y) → map (f ∘C g) ≈ map f ∘D map g

Id : ∀ {a b c} {C : Cat a b c} → Fun C C
Id {C = C} = record
  { Map      = λ x → x
  ; map      = λ f → f
  ; cong-map = λ f=g → f=g
  ; resp-id  = ≈refl
  ; resp-∘   = λ _ _ → ≈refl }
  where open Cat C

_○_ : ∀ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} {E : Cat c c₁ c₂} →
         Fun D E → Fun C D → Fun C E
_○_ {E = E} F G = record
  { Map      = λ A → Map F (Map G A)
  ; map      = λ f → map F (map G f)
  ; cong-map = λ f=g → cong-map F (cong-map G f=g)
  ; resp-id  = cong-map F (resp-id G) ⟨≈⟩ resp-id F
  ; resp-∘   = λ f g → cong-map F (resp-∘ G f g) ⟨≈⟩ resp-∘ F (map G f) (map G g) }
  where
    open Fun
    open Cat E

module _ {a a₁ a₂ b b₁ b₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} where

  open Cat using (Obj)
  open Fun

  private
    _⇒C_ = Cat._⇒_ C
    _⇒D_ = Cat._⇒_ D
  open Cat D hiding (Obj)

  record NatTrans (F G : Fun C D) : Set (a ⊔ a₁ ⊔ b₁ ⊔ b₂) where
    field
      η : ∀ (X : Obj C) → Map F X ⇒D Map G X
      naturality : ∀ {X Y : Obj C} (f : X ⇒C Y) → map G f ∘ η X ≈ η Y ∘ map F f

  idNat : ∀ {F : Fun C D} → NatTrans F F
  idNat {F} = record
    { η = λ _ → id
    ; naturality = λ f → idR (map F f) ⟨≈⟩ʳ idL (map F f) }

  _∘Nat_ : ∀ {F G H : Fun C D} → NatTrans G H → NatTrans F G → NatTrans F H
  _∘Nat_ {F} {G} {H} f g = record
    { η = λ X → η f X ∘ η g X
    ; naturality = λ h →
      assoc _ _ _ ʳ⟨≈⟩
      cong∘L (naturality f h) ⟨≈⟩
      assoc _ _ _ ⟨≈⟩
      cong∘R (naturality g h) ⟨≈⟩ʳ
      assoc _ _ _
    }
    where open NatTrans

  record NatIso (F G : Fun C D) : Set (a ⊔ a₁ ⊔ b₁ ⊔ b₂) where
    open NatTrans
    field
      to   : NatTrans F G
      from : NatTrans G F
      idF  : ∀ (X : Obj C) → η from X ∘ η to X ≈ id
      idG  : ∀ (X : Obj C) → η to X ∘ η from X ≈ id

  _≋_ = NatIso

  open NatIso
  open NatTrans

  ≋refl : {F : Fun C D} → F ≋ F
  ≋refl = record
    { to   = idNat
    ; from = idNat
    ; idF  = λ _ → idL _
    ; idG  = λ _ → idL _ }

  ≋sym : {F G : Fun C D} → F ≋ G → G ≋ F
  ≋sym F=G = record
    { to   = from F=G
    ; from = to F=G
    ; idF  = idG F=G
    ; idG  = idF F=G }

  ≋trans : {F G H : Fun C D} → F ≋ G → G ≋ H → F ≋ H
  ≋trans F=G G=H = record
    { to   = to G=H ∘Nat to F=G
    ; from = from F=G ∘Nat from G=H
    ; idF  = λ _ →
      assoc _ _ _ ⟨≈⟩
      cong∘R (assoc _ _ _ ʳ⟨≈⟩ cong∘L (idF G=H _) ⟨≈⟩ idL _) ⟨≈⟩
      idF F=G _
    ; idG  = λ _ →
      assoc _ _ _ ⟨≈⟩
      cong∘R (assoc _ _ _ ʳ⟨≈⟩ cong∘L (idG F=G _) ⟨≈⟩ idL _) ⟨≈⟩
      idG G=H _
    }

  ≋Equiv : IsEquivalence _≋_
  ≋Equiv = record
    { ≈refl  = ≋refl
    ; ≈sym   = ≋sym
    ; ≈trans = ≋trans
    }

      