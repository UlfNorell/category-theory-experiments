
module Category.CAT where

open import Prelude hiding (id; _∘_; map)
open import Category.Base
open import Category.Functor
open import Category.Isomorphism

CAT : ∀ a b c → Cat _ _ _
CAT a b c = record
  { Obj = Cat a b c
  ; _⇒_ = Fun
  ; id = Id
  ; _∘_ = _○_
  ; _≈_ = _≋_
  ; isEquiv = ≋Equiv
  ; idL   = λ {C D} F →
    let open Cat C using () renaming (Obj to ObjC; _⇒_ to _⇒C_)
        open Cat D
    in record
    { to = record
      { η = λ X → id
      ; naturality = λ f → idR _ ⟨≈⟩ʳ idL _ }
    ; from = record
      { η = λ X → id
      ; naturality = λ f → idR _ ⟨≈⟩ʳ idL _ }
    ; idF = λ _ → idL _
    ; idG = λ _ → idL _ }
  ; idR   = λ {C D} F →
    let open Cat C using () renaming (Obj to ObjC; _⇒_ to _⇒C_)
        open Cat D
    in record
    { to = record
      { η = λ X → id
      ; naturality = λ f → idR _ ⟨≈⟩ʳ idL _ }
    ; from = record
      { η = λ X → id
      ; naturality = λ f → idR _ ⟨≈⟩ʳ idL _ }
    ; idF = λ _ → idL _
    ; idG = λ _ → idL _ }
  ; cong∘ = λ {C D E F F′ G G′} F=F′ G=G′ →
    record
    { to   = lift○ (to F=F′) (to G=G′)
    ; from = lift○ (from F=F′) (from G=G′)
    ; idF  = λ X → id○ F=F′ G=G′
    ; idG  = λ X → id○ (≋sym F=F′) (≋sym G=G′) }
  ; assoc = λ {A B C D} F G H →
    let open Cat D
    in record
    { to   = record { η = λ _ → id; naturality = λ _ → idR _ ⟨≈⟩ʳ idL _ }
    ; from = record { η = λ _ → id; naturality = λ _ → idR _ ⟨≈⟩ʳ idL _ }
    ; idF  = λ _ → idL _
    ; idG  = λ _ → idL _ }
  }
  where
    open NatTrans
    open NatIso
    open Fun

    module _ {a a₁ a₂ b b₁ b₂ c c₁ c₂} {C : Cat a a₁ a₂} {D : Cat b b₁ b₂} {E : Cat c c₁ c₂}
             {F F′ : Fun D E} {G G′ : Fun C D} where
      open Cat E
      lift○ : NatTrans F F′ → NatTrans G G′ → NatTrans (F ○ G) (F′ ○ G′)
      lift○ f g = record
        { η = λ _ → map F′ (η g _) ∘ η f _
        ; naturality = λ h →
          assoc _ _ _ ʳ⟨≈⟩
          cong∘L (resp-∘ F′ _ _ ʳ⟨≈⟩ cong-map F′ (naturality g h)) ⟨≈⟩
          naturality f _ ⟨≈⟩
          cong∘R (resp-∘ F _ _) ⟨≈⟩
          assoc _ _ _ ʳ⟨≈⟩ʳ
          cong∘L (naturality f _)
        }

      id○ : ∀ {X} (F=F′ : F ≋ F′) (G=G′ : G ≋ G′) →
            (map F (η (from G=G′) X) ∘ η (from F=F′) (Map G′ X)) ∘
            (map F′ (η (to G=G′) X) ∘ η (to F=F′) (Map G X)) ≈ id
      id○ F=F′ G=G′ =
        cong∘L (naturality (from F=F′) _) ⟨≈⟩
        assoc _ _ _ ⟨≈⟩
        cong∘R (assoc _ _ _ ʳ⟨≈⟩
                cong∘L (resp-∘ F′ _ _ ʳ⟨≈⟩
                        cong-map F′ (idF G=G′ _) ⟨≈⟩
                        resp-id F′) ⟨≈⟩
                idL _) ⟨≈⟩
        idF F=F′ _
