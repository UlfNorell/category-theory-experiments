
module Category.Yoneda2 where

open import Prelude hiding (id; _∘_; map)
open import Category.Base
open import Category.Functor
open import Category.SETOID
open import Category.FUN
open import Category.Isomorphism
open import Category.Cross
open import Logic.Setoid
open import Logic.Equivalence
import Category.HomFunctor as HomFunctor

open Cat using (Obj)
open Fun
open _⇒ˢ_
open _≈ˢ_

module CatAndHom {a b c} (C : Cat a b c) where
  open Cat C public
  open HomFunctor C public

module _ {a} (C : Cat a a a) where

  open Cat using (Hom)
  module C = CatAndHom C

  open NatTrans

  SET = SETOID a a
  SET^C = FUN C SET
  SET^C×C = FUN C SET [×] C

  module S = CatAndHom SET
  module F = CatAndHom (FUN C SET)

  module SET^C = CatAndHom SET^C   -- display form for Hom functors not working!

  open S hiding (Obj; Hom)

  I : Fun C SET → Fun C SET
  I G = SET^C.Hom[-, G ] ʳ○ C.HomFUN

  J : Obj C → Fun SET^C SET
  J X = SET^C.Hom[ C.Hom[ X ,-] ,-]

  LHS : Fun SET^C×C SET
  Map LHS (F , X) = SET^C.Hom C.Hom[ X ,-] F
  map LHS {F , X} {G , Y} (α , f) = map (I G) f ∘ map (J X) α
  cong-map LHS {F , X} {G , Y} {α , f} {β , g} (α=β , f=g) =
    cong-map (I G) f=g ∘≈ cong-map (J X) α=β
  resp-id LHS {F , X} =
    resp-id (I F) ∘≈ resp-id (J X) ⟨≈⟩ idL
  resp-∘ LHS {F , X} {G , Y} {H , Z} (α , f) (β , g) =
    resp-∘ (I H) f g ∘≈ resp-∘ (J X) α β ⟨≈⟩
    assoc ⟨≈⟩
    cong∘R (assoc ʳ⟨≈⟩ cong∘L (natural (map SET^C.HomFUN (map C.HomFUN g)) α) ʳ⟨≈⟩ assoc) ⟨≈⟩ʳ
    assoc

  RHS : Fun SET^C×C (SETOID a a)
  Map RHS (F , X) = Map F X
  map RHS {F , X} {G , Y} (α , f) = map G f ∘ η α X
  cong-map RHS {F , X} {G , Y} {α , f} {β , g} (α=β , f=g) = cong-map G f=g ∘≈ α=β X
  resp-id RHS {F , X} = idR ⟨≈⟩ resp-id F
  resp-∘ RHS {F , X} {G , Y} {H , Z} (α , f) (β , g) =
    cong∘L (resp-∘ H f g) ⟨≈⟩
    assoc ⟨≈⟩ 
    cong∘R (assoc ʳ⟨≈⟩ cong∘L (natural α g) ⟨≈⟩ assoc) ⟨≈⟩ʳ
    assoc

  -- apply₁ : (F G : Fun C SET) (Y : Obj C) (X : Obj SET) → Setoid.Carrier (Map F Y) →
  --          (X ⇒ˢ SET^C.Hom F G) → X ⇒ˢ Map G Y
  -- app (apply₁ F G Y X y f) x = η (f ∙ x) _ ∙ y
  -- ext (apply₁ F G Y X x f) x=y = {!ext (η (app f _) Y) ?!}

  -- applyH : (F G : Fun C SET) (X : Obj C) (x : Setoid.Carrier (Map G X)) →
  --          Hom SET^C G F ⇒ˢ Map F X
  -- app (applyH F G X x) α = η α X ∙ x
  -- ext (applyH F G X x) α=β = α=β X ∙≈ Setoid.≈refl (Map G X)

  -- yoneda : Iso (FUN SET^C×C (SETOID a a)) LHS RHS
  -- η (Iso.to yoneda) (F , X) = applyH F C.Hom[ X ,-] X C.id
  -- natural (Iso.to yoneda) {F , X} {G , Y} (α , f) =
  --   cong∘L (natural α f) ⟨≈⟩ {!!}
  -- η (Iso.from yoneda) (F , X) = {!!}
  -- natural (Iso.from yoneda) f = {!!}
  -- Iso.ida yoneda X = {!!}
  -- Iso.idb yoneda X = {!!}

  yoneda : Iso (FUN SET^C×C (SETOID a a)) LHS RHS

  app (η (Iso.to yoneda) (F , X)) α = η α X ∙ C.id
  ext (η (Iso.to yoneda) (F , X)) {α} {β} α=β = α=β X ∙≈ Cat.≈refl C
  ≈ext (natural (Iso.to yoneda) {F , X} {G , Y} (α , f)) {β} {γ} β=γ =
    let module GY = IsEquivalence (Setoid.isEquiv (Map G Y))
        module FY = IsEquivalence (Setoid.isEquiv (Map F Y)) in
    natural α f ∙≈ β=γ X ∙≈ C.≈refl GY.⟨≈⟩
    reflˢ (η α Y) ∙≈ (natural γ f ∙≈ C.≈refl FY.⟨≈⟩
    reflˢ (η γ Y) ∙≈ C.idRL)

  app (η (app (η (Iso.from yoneda) (F , X)) x) Y) f = map F f ∙ x
  ext (η (app (η (Iso.from yoneda) (F , X)) x) Y) f = cong-map F f ∙≈ Setoid.≈refl (Map F X)
  ≈ext (natural (app (η (Iso.from yoneda) (F , X)) x) {Y} {Z} f) {i} {j} i=j =
    let module FZ = IsEquivalence (Setoid.isEquiv (Map F Z))
        module FX = IsEquivalence (Setoid.isEquiv (Map F X)) in
    resp-∘ F f i ∙≈ FX.≈refl FZ.ʳ⟨≈⟩
    cong-map F (C.cong∘R i=j) ∙≈ FX.≈refl
  ≈ext (ext (η (Iso.from yoneda) (F , X)) x=y Y) {i} {j} i=j = cong-map F i=j ∙≈ x=y
  ≈ext (≈ext (natural (Iso.from yoneda) {F , X} {G , Y} (α , f)) {x} {y} x=y Z) {i} {j} i=j =
    let module GY = IsEquivalence (Setoid.isEquiv (Map G Y))
        module GZ = IsEquivalence (Setoid.isEquiv (Map G Z))
        module GX = IsEquivalence (Setoid.isEquiv (Map G X))
        module FX = IsEquivalence (Setoid.isEquiv (Map F X)) in
    natural α (i C.∘ f) ∙≈ FX.≈sym x=y GZ.ʳ⟨≈⟩
    resp-∘ G _ _ ∙≈ GX.≈refl GZ.⟨≈⟩ cong-map G i=j ∙≈ GY.≈refl

  ≈ext (≈ext (Iso.ida yoneda (F , X)) {α} {β} α=β Y) {f} {g} f=g =
    let module FY = IsEquivalence (Setoid.isEquiv (Map F Y)) in
    natural α f ∙≈ C.≈refl FY.⟨≈⟩ α=β Y ∙≈ C.idR FY.⟨≈⟩ ext (η β Y) f=g
  ≈ext (Iso.idb yoneda (F , X)) {x} {y} x=y = resp-id F ∙≈ x=y
