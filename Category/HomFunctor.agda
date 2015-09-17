
open import Category.Base

module Category.HomFunctor {a b c} (C : Cat a b c) where

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
open NatTrans

open Cat C hiding (Obj)
private SET = SETOID b c
private module S = Cat SET

Hom[-,-] : Fun (C op [×] C) SET
Map Hom[-,-] X = Hom (fst X) (snd X)
app (map Hom[-,-] (f , g)) h = g ∘ h ∘ f
ext (map Hom[-,-] (f , g)) h=k = cong∘L (cong∘R h=k)
≈ext (cong-map Hom[-,-] {f = f , g} {f₁ , g₁} (f=f₁ , g=g₁)) x=y = g=g₁ ∘≈ x=y ∘≈ f=f₁
≈ext (resp-id Hom[-,-]) x=y = idR ⟨≈⟩ idL ⟨≈⟩ x=y 
≈ext (resp-∘ Hom[-,-] (f , g) (f₁ , g₁)) x=y =
  assoc ⟨≈⟩ cong∘R (cong∘L x=y) ⟨≈⟩ assoc ⟨≈⟩ʳ assoc ⟨≈⟩ cong∘R (assoc ⟨≈⟩ assoc)

Hom[_,-] : Obj C → Fun C SET
Map Hom[ X ,-] Y                    = Hom X Y
app (map Hom[ X ,-] f) g            = f ∘ g
ext (map Hom[ X ,-] f) g            = cong∘R g
≈ext (cong-map Hom[ X ,-] f=g) x=y = cong∘ f=g x=y
≈ext (resp-id Hom[ X ,-]) x=y      = idL ⟨≈⟩ x=y
≈ext (resp-∘ Hom[ X ,-] f g) x=y   = assoc ⟨≈⟩ cong∘R (cong∘R x=y)

Hom[-,_] : Obj C → Fun (C op) SET
Map Hom[-, X ] Y                   = Hom Y X
app (map Hom[-, X ] f) g           = g ∘ f
ext (map Hom[-, X ] f) g=h         = cong∘L g=h
≈ext (cong-map Hom[-, X ] f=g) i=j = cong∘ i=j f=g
≈ext (resp-id Hom[-, X ]) x=y      = idR ⟨≈⟩ x=y
≈ext (resp-∘ Hom[-, X ] f g) x=y   = cong∘L x=y ⟨≈⟩ʳ assoc 

-- Hom(X,-) is a cofunctor from C to FUN C SET
HomFUN : Fun (C op) (FUN C SET)
Map HomFUN X = Hom[ X ,-]
η (map HomFUN f) X = map Hom[-, X ] f
≈ext (natural (map HomFUN f) g) i=j = assoc ʳ⟨≈⟩ cong∘L (cong∘R i=j)
cong-map HomFUN f=g Z = cong-map Hom[-, Z ] f=g
resp-id  HomFUN Z     = resp-id  Hom[-, Z ]
resp-∘   HomFUN f g Z = resp-∘   Hom[-, Z ] f g

coHomFUN : Fun C (FUN (C op) SET)
Map coHomFUN X = Hom[-, X ]
η (map coHomFUN f) X = map Hom[ X ,-] f
≈ext (natural (map coHomFUN f) g) i=j = assoc ⟨≈⟩ cong∘R (cong∘L i=j)
cong-map coHomFUN f=g Z = cong-map Hom[ Z ,-] f=g
resp-id coHomFUN Z = resp-id Hom[ Z ,-]
resp-∘ coHomFUN f g Z = resp-∘ Hom[ Z ,-] f g
