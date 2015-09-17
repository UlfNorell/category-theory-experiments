
open import Category.Base

module Category.Tactic {a b c} (C : Cat a b c) where

open import Prelude hiding (id; _∘_)
open Cat C
open import Data.List

data Ty : Set a where
  _`⇒_ : Obj → Obj → Ty

⟦_⟧ty : Ty → Set b
⟦ X `⇒ Y ⟧ty = X ⇒ Y

Cxt = List Ty

data Rep (Γ : Cxt) : Obj → Obj → Set a where
  var  : ∀ {X Y} → (X `⇒ Y) ∈ Γ → Rep Γ X Y
  _`∘_ : ∀ {X Y Z} → Rep Γ Y Z → Rep Γ X Y → Rep Γ X Z
  `id  : ∀ {X} → Rep Γ X X

Env : Cxt → Set _
Env Γ = All ⟦_⟧ty Γ

⟦_⟧ : ∀ {Γ X Y} → Rep Γ X Y → Env Γ → X ⇒ Y
⟦ var x   ⟧ ρ = lookup∈ ρ x
⟦ r `∘ r₁ ⟧ ρ = ⟦ r ⟧ ρ ∘ ⟦ r₁ ⟧ ρ
⟦ `id     ⟧ ρ = id
