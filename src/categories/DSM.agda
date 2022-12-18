{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories

module categories.DSM {ℓₒ ℓₘ} {Ob : Type ℓₒ} (C : WildSemicategoryStructure ℓₒ ℓₘ Ob) where

open WildSemicategoryStructure C

DSM : Ob → Type (ℓₒ l⊔ ℓₘ)
DSM x = (y : Ob) → hom x y → Bool

DSM= : {x : Ob} {σ τ : DSM x} → (∀ y → (f : hom x y) → σ y f == τ y f) → σ == τ
DSM= = λ=₂

infix 30 _∋_
_∋_ : {x y : Ob} → DSM x → hom x y → Bool
_∋_ {y = y} σ f = σ y f

infix 50 _·_
_·_ : {x y : Ob} → DSM x → hom x y → DSM y
_·_ {x} {y} σ f _ g = σ ∋ g ◦ f
