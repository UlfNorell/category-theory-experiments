{-# OPTIONS --copatterns #-}
module Category.Functor where

open import Prelude hiding (id; _∘_; map)
open import Logic.Equivalence
open import Category.Base
open import Category.Isomorphism
open import Category.Finite

open Cat using (Obj)

record Fun {a₁ a₂ a₃ b₁ b₂ b₃} (C : Cat a₁ a₂ a₃) (D : Cat b₁ b₂ b₃) : Set (a₁ ⊔ a₂ ⊔ a₃ ⊔ b₁ ⊔ b₂ ⊔ b₃) where
  no-eta-equality
  open Cat
  private module C = Cat C
  private module D = Cat D
  field
    Map     : Obj C → Obj D
    map     : ∀ {X Y : Obj C} → (X C.⇒ Y) → (Map X D.⇒ Map Y)
    cong-map : ∀ {X Y : Obj C} {f g : X C.⇒ Y} → f C.≈ g →  map f D.≈ map g
    resp-id : ∀ {X : Obj C} → map (C.id {X}) D.≈ D.id
    resp-∘  : ∀ {X Y Z : Obj C} (f : Y C.⇒ Z) (g : X C.⇒ Y) → map (f C.∘ g) D.≈ map f D.∘ map g

module _ {a b c} {C : Cat a b c} where

  open Cat C
  open Fun

  Id : Fun C C
  Map      Id x   = x
  map      Id f   = f
  cong-map Id f=g = f=g
  resp-id  Id     = ≈refl
  resp-∘   Id _ _ = ≈refl

module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {A : Cat a a₁ a₂} {B : Cat b b₁ b₂} {C : Cat c c₁ c₂} where

  open Fun
  private module A = Cat A
  private module B = Cat B
  open Cat C

  infixl 9 _○_
  _○_ : Fun B C → Fun A B → Fun A C
  Map      (F ○ G) X   = Map F (Map G X)
  map      (F ○ G) f   = map F (map G f)
  cong-map (F ○ G) eq  = cong-map F (cong-map G eq)
  resp-id  (F ○ G)     = cong-map F (resp-id G) ⟨≈⟩ resp-id F
  resp-∘   (F ○ G) f g = cong-map F (resp-∘ G f g) ⟨≈⟩ resp-∘ F (map G f) (map G g)

  _ʳ○_ : Fun (B op) C → Fun (A op) B → Fun A C
  Map (F ʳ○ G) X = Map F (Map G X)
  map (F ʳ○ G) f = map F (map G f) 
  cong-map (F ʳ○ G) f=g = cong-map F (cong-map G f=g)
  resp-id (F ʳ○ G) = cong-map F (resp-id G) ⟨≈⟩ resp-id F 
  resp-∘ (F ʳ○ G) f g = cong-map F (resp-∘ G g f) ⟨≈⟩ resp-∘ F (map G f) (map G g)

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
  resp-∘   (Const X) _ _ = ≈sym idL

  record NatTrans (F G : Fun C D) : Set (a ⊔ a₁ ⊔ b₁ ⊔ b₂) where
    no-eta-equality
    field
      η : ∀ (X : Obj C) → Map F X ⇒D Map G X
      natural : ∀ {X Y : Obj C} (f : X ⇒C Y) → map G f ∘ η X ≈ η Y ∘ map F f

  open NatTrans
  idNat : ∀ {F : Fun C D} → NatTrans F F
  η          idNat _ = id
  natural idNat _ = idRL

  infixl 9 _∘Nat_
  _∘Nat_ : ∀ {F G H : Fun C D} → NatTrans G H → NatTrans F G → NatTrans F H
  η          (f ∘Nat g) X = η f X ∘ η g X
  natural (f ∘Nat g) h =
    assoc ʳ⟨≈⟩
    cong∘L (natural f h) ⟨≈⟩
    assoc ⟨≈⟩
    cong∘R (natural g h) ⟨≈⟩ʳ
    assoc

  record NatIso (F G : Fun C D) : Set (a ⊔ a₁ ⊔ b₁ ⊔ b₂) where
    open NatTrans
    field
      to   : NatTrans F G
      from : NatTrans G F
      idF  : ∀ {X : Obj C} → η from X ∘ η to X ≈ id
      idG  : ∀ {X : Obj C} → η to X ∘ η from X ≈ id

  infix 4 _≋_
  _≋_ = NatIso

  open NatIso
  open NatTrans

  ≋refl : {F : Fun C D} → F ≋ F
  to   ≋refl = idNat
  from ≋refl = idNat
  idF  ≋refl = idL
  idG  ≋refl = idL

  ≋sym : {F G : Fun C D} → F ≋ G → G ≋ F
  to   (≋sym F=G) = from F=G
  from (≋sym F=G) = to F=G
  idF  (≋sym F=G) = idG F=G
  idG  (≋sym F=G) = idF F=G

  ≋trans : {F G H : Fun C D} → F ≋ G → G ≋ H → F ≋ H
  to   (≋trans F=G G=H) = to G=H ∘Nat to F=G
  from (≋trans F=G G=H) = from F=G ∘Nat from G=H
  idF  (≋trans F=G G=H) =
    assoc ⟨≈⟩
    cong∘R (assoc ʳ⟨≈⟩ cong∘L (idF G=H) ⟨≈⟩ idL) ⟨≈⟩
    idF F=G
  idG  (≋trans F=G G=H) =
    assoc ⟨≈⟩
    cong∘R (assoc ʳ⟨≈⟩ cong∘L (idG F=G) ⟨≈⟩ idL) ⟨≈⟩
    idG G=H

  ≋Equiv : IsEquivalence _≋_
  IsEquivalence.≈refl  ≋Equiv = ≋refl
  IsEquivalence.≈sym   ≋Equiv = ≋sym
  IsEquivalence.≈trans ≋Equiv = ≋trans

module _ {a a₁ a₂} {C : Cat a a₁ a₂} where

  Const₁ : (X : Obj C) → Fun One C
  Const₁ X = Const X
