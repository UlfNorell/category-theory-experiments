{-# OPTIONS --copatterns #-}
module Category.Functor where

open import Prelude hiding (id; _∘_; map)
open import Logic.Equivalence
open import Category.Base
open import Category.Isomorphism
open import Category.Finite

open Cat using (Obj)

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
{-# NO_ETA Fun #-}

module _ {a b c} {C : Cat a b c} where

  open Cat C
  open Fun

  Id : Fun C C
  Map      Id x   = x
  map      Id f   = f
  cong-map Id f=g = f=g
  resp-id  Id     = ≈refl
  resp-∘   Id _ _ = ≈refl

module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} {E : Cat c c₁ c₂} where

  open Fun
  open Cat E

  infixl 9 _○_
  _○_ : Fun D E → Fun C D → Fun C E
  Map      (F ○ G) A   = Map F (Map G A)
  map      (F ○ G) f   = map F (map G f)
  cong-map (F ○ G) eq  = cong-map F (cong-map G eq)
  resp-id  (F ○ G)     = cong-map F (resp-id G) ⟨≈⟩ resp-id F
  resp-∘   (F ○ G) f g = cong-map F (resp-∘ G f g) ⟨≈⟩ resp-∘ F (map G f) (map G g)

module _ {a a₁ a₂ b b₁ b₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} where

  open Cat using (Obj)
  open Fun

  private
    _⇒C_ = Cat._⇒_ C
    _⇒D_ = Cat._⇒_ D
  open Cat D hiding (Obj)

  Const : (X : Obj D) → Fun C D
  Map      (Const X) _   = X
  map      (Const X) _   = id
  cong-map (Const X) _   = ≈refl
  resp-id  (Const X)     = ≈refl
  resp-∘   (Const X) _ _ = ≈sym (idL _)

  record NatTrans (F G : Fun C D) : Set (a ⊔ a₁ ⊔ b₁ ⊔ b₂) where
    field
      η : ∀ (X : Obj C) → Map F X ⇒D Map G X
      naturality : ∀ {X Y : Obj C} (f : X ⇒C Y) → map G f ∘ η X ≈ η Y ∘ map F f
  {-# NO_ETA NatTrans #-}

  open NatTrans
  idNat : ∀ {F : Fun C D} → NatTrans F F
  η          idNat _ = id
  naturality idNat _ = idRL

  _∘Nat_ : ∀ {F G H : Fun C D} → NatTrans G H → NatTrans F G → NatTrans F H
  η          (f ∘Nat g) X = η f X ∘ η g X
  naturality (f ∘Nat g) h =
    assoc _ _ _ ʳ⟨≈⟩
    cong∘L (naturality f h) ⟨≈⟩
    assoc _ _ _ ⟨≈⟩
    cong∘R (naturality g h) ⟨≈⟩ʳ
    assoc _ _ _

  record NatIso (F G : Fun C D) : Set (a ⊔ a₁ ⊔ b₁ ⊔ b₂) where
    open NatTrans
    field
      to   : NatTrans F G
      from : NatTrans G F
      idF  : ∀ (X : Obj C) → η from X ∘ η to X ≈ id
      idG  : ∀ (X : Obj C) → η to X ∘ η from X ≈ id
  {-# NO_ETA NatIso #-}

  infix 4 _≋_
  _≋_ = NatIso

  open NatIso
  open NatTrans

  ≋refl : {F : Fun C D} → F ≋ F
  to   ≋refl   = idNat
  from ≋refl   = idNat
  idF  ≋refl _ = idL _
  idG  ≋refl _ = idL _

  ≋sym : {F G : Fun C D} → F ≋ G → G ≋ F
  to   (≋sym F=G) = from F=G
  from (≋sym F=G) = to F=G
  idF  (≋sym F=G) = idG F=G
  idG  (≋sym F=G) = idF F=G

  ≋trans : {F G H : Fun C D} → F ≋ G → G ≋ H → F ≋ H
  to   (≋trans F=G G=H)   = to G=H ∘Nat to F=G
  from (≋trans F=G G=H)   = from F=G ∘Nat from G=H
  idF  (≋trans F=G G=H) _ =
    assoc _ _ _ ⟨≈⟩
    cong∘R (assoc _ _ _ ʳ⟨≈⟩ cong∘L (idF G=H _) ⟨≈⟩ idL _) ⟨≈⟩
    idF F=G _
  idG  (≋trans F=G G=H) _ =
    assoc _ _ _ ⟨≈⟩
    cong∘R (assoc _ _ _ ʳ⟨≈⟩ cong∘L (idG F=G _) ⟨≈⟩ idL _) ⟨≈⟩
    idG G=H _

  ≋Equiv : IsEquivalence _≋_
  IsEquivalence.≈refl  ≋Equiv = ≋refl
  IsEquivalence.≈sym   ≋Equiv = ≋sym
  IsEquivalence.≈trans ≋Equiv = ≋trans

module _ {a a₁ a₂} {C : Cat a a₁ a₂} where

  ObjFun : (X : Obj C) → Fun One C
  ObjFun X = Const X
