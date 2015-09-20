
open import Category.Base

module Category.Yoneda where

open import Prelude hiding (id; _∘_; map)
open import Category.Functor
open import Category.SETOID
open import Category.FUN
open import Category.Isomorphism
open import Category.Cross
open import Logic.Setoid
open import Logic.Equivalence

open Cat using (Obj)
open Fun
open _⇒ˢ_
open _≈ˢ_

module _ {a b c} (C : Cat a b c) where

  open Cat C hiding (Obj)

  HomFun : Obj C → Fun C (SETOID b c)
  Map (HomFun X) Y                    = Hom X Y
  app (map (HomFun X) f) g            = f ∘ g
  ext (map (HomFun X) f) g            = cong∘R g
  ≈ext (cong-map (HomFun X) f=g) x=y = cong∘ f=g x=y
  ≈ext (resp-id (HomFun X)) x=y      = idL ⟨≈⟩ x=y
  ≈ext (resp-∘ (HomFun X) f g) x=y   = assoc ⟨≈⟩ cong∘R (cong∘R x=y)

module _ {a} (C : Cat a a a) where

  open Cat using (Hom)
  open Cat C hiding (Obj; Hom; ≈refl; ≈sym; ≈trans; _⟨≈⟩ʳ_)

  -- For each object A of C, the natural transformations from hA to F are in one-to-one correspondence with the elements of F(A).
  -- That is, \mathrm{Nat}(h^A,F) \cong F(A).

  open NatTrans

  Set^C×C = FUN C (SETOID a a) [×] C

  LHS : Fun Set^C×C (SETOID a a)
  Map LHS (F , X) = Hom (FUN C (SETOID a a)) (HomFun C X) F   -- setoid of natural transformations HomFun X → F
  app (η (app (map LHS {F , X} {G , Y} (f , g)) h) Z) i = map G i ∙ η f Y ∙ η h Y ∙ g
  ext (η (app (map LHS {F , X} {G , Y} (f , g)) h) Z) i = cong-map G i ∙≈ Setoid.≈refl (Map G Y)
  ≈ext (natural (app (map LHS {F , X} {G , Y} (f , g)) h) {Z} {W} i) {j} {k} j=k =
    let open IsEquivalence (Setoid.isEquiv (Map G W)) in
    reflˢ (map G i) ∙≈ cong-map G j=k ∙≈ Setoid.≈refl (Map G Y) ⟨≈⟩
    ≈sym (resp-∘ G i k ∙≈ Setoid.≈refl (Map G Y))
  ≈ext (ext (map LHS {X = F , X} {G , Y} (f , g)) h Z) {i} {j} i=j =
    cong-map G i=j ∙≈ reflˢ (η f Y) ∙≈ h Y ∙≈ Setoid.≈refl (Hom C X Y)
  ≈ext (≈ext (cong-map LHS {F , X} {G , Y} {f , g} {f′ , g′} (f=f′ , g=g′)) {i} {j} i=j Z) {h} {k} h=k =
    cong-map G h=k ∙≈ f=f′ Y ∙≈ i=j Y ∙≈ g=g′
  ≈ext (≈ext (resp-id LHS {F , X}) {f} {g} f=g Y) {i} {j} i=j =
    let open IsEquivalence (Setoid.isEquiv (Map F Y)) in
    ≈ext (natural f i) (Cat.≈refl C) ⟨≈⟩ f=g Y ∙≈ Cat.≈trans C idR i=j
  ≈ext (≈ext (resp-∘ LHS {F , X} {G , Y} {H , Z} (f , g) (i , j)) {h} {k} h=k W) {s} {t} s=t =
    let open IsEquivalence (Setoid.isEquiv (Map G Z)) in
    cong-map H s=t ∙≈ reflˢ (η f Z) ∙≈ ≈sym (natural i g ∙≈ Setoid.≈sym (Map F Y) (h=k Y ∙≈ Cat.≈refl C) ⟨≈⟩
    reflˢ (η i Z) ∙≈ natural h g ∙≈ Cat.≈refl C) 

  RHS : Fun Set^C×C (SETOID a a)
  Map RHS (F , X) = Map F X
  app (map RHS {X = F , X} {G , Y} (f , g)) x = map G g ∙ η f X ∙ x
  ext (map RHS {X = F , X} {G , Y} (f , g)) x = map G g ⊜ η f X ⊜ x
  ≈ext (cong-map RHS {X = F , X} {G , Y} {f = f , i} {g , j} (f=g , i=j)) x=y =
    ≈ext (cong-map G i=j) (≈ext (f=g X) x=y)
  ≈ext (resp-id RHS {F , X}) x=y = ≈ext (resp-id F) x=y
  ≈ext (resp-∘ RHS {F , X} {G , Y} {H , Z} (f , i) (g , j)) x=y =
    let open IsEquivalence (Setoid.isEquiv (Map H Z))
    in ≈ext (resp-∘ H i j) (ext (η f X) (Setoid.≈refl (Map G X))) ⟨≈⟩
       map H i ⊜ ≈ext (natural f j) (η g X ⊜ x=y)

  yoneda : Iso (FUN Set^C×C (SETOID a a)) LHS RHS
  app (η (Iso.to yoneda) (F , X)) α = η α X ∙ id
  ext (η (Iso.to yoneda) (F , X)) {α} {β} α=β = α=β X ∙≈ Cat.≈refl C
  ≈ext (natural (Iso.to yoneda) {F , X} {G , Y} (α , f)) {β} {γ} β=γ =
    let open IsEquivalence (Setoid.isEquiv (Map G Y)) in
    natural α f ∙≈ β=γ X ∙≈ Cat.≈refl C ⟨≈⟩ʳ resp-id G ∙≈ reflˢ (η α Y) ∙≈
      Setoid.≈sym (Map F Y) (Setoid.≈trans (Map F Y) (natural γ f ∙≈ Cat.≈refl C) (reflˢ (η γ Y) ∙≈ idR))
  app (η (app (η (Iso.from yoneda) (F , X)) x) Y) f = map F f ∙ x
  ext (η (app (η (Iso.from yoneda) (F , X)) x) Y) f = cong-map F f ∙≈ Setoid.≈refl (Map F X)
  ≈ext (natural (app (η (Iso.from yoneda) (F , X)) x) {Y} {Z} f) {i} {j} i=j =
    let open IsEquivalence (Setoid.isEquiv (Map F Z)) in
    ≈sym (resp-∘ F f j ∙≈ Setoid.≈refl (Map F X) ⟨≈⟩
    reflˢ (map F f) ∙≈ cong-map F (Cat.≈sym C i=j) ∙≈ Setoid.≈refl (Map F X))
  ≈ext (ext (η (Iso.from yoneda) (F , X)) x=y Y) {i} {j} i=j = cong-map F i=j ∙≈ x=y
  ≈ext (≈ext (natural (Iso.from yoneda) {F , X} {G , Y} (α , f)) {x} {y} x=y Z) {i} {j} i=j =
    let open IsEquivalence (Setoid.isEquiv (Map G Y)) in
    cong-map G i=j ∙≈ ≈sym (natural α f ∙≈ Setoid.≈sym (Map F X) x=y ⟨≈⟩ ≈refl)
  ≈ext (≈ext (Iso.ida yoneda (F , X)) {α} {β} α=β Y) {f} {g} f=g =
    let open IsEquivalence (Setoid.isEquiv (Map F Y)) in
    natural α f ∙≈ Cat.≈refl C ⟨≈⟩
    α=β Y ∙≈ Cat.≈trans C idR f=g
  ≈ext (Iso.idb yoneda (F , X)) {x} {y} x=y = resp-id F ∙≈ x=y
