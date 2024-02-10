{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories

module categories.DSM {ℓₒ ℓₘ}
  {Ob : Type ℓₒ}
  (C : WildSemicategoryStructure ℓₒ ℓₘ Ob)
  where

open WildSemicategoryStructure C

-- Decidable sets of morphisms

DSM : Ob → Type (ℓₒ ∪ ℓₘ)
DSM x = (y : Ob) → hom x y → Bool

⦅_⦆ : ∀ {x} → (∀ {y} → hom x y → Bool) → DSM x
⦅ χ ⦆ y f = χ f

infix 30 _∋_ _ϵ_

_∋_ : ∀ {x y} → hom x y → DSM x → Bool
_∋_ {x} {y} f D = D y f

_ϵ_ : ∀ {x y} → hom x y → DSM x → Type₀
f ϵ D = is-true (f ∋ D)

_ϵ/_ : ∀ {x y} → hom x y → DSM x → Type₀
f ϵ/ D = ¬ (f ϵ D)

ϵ-dec : ∀ {x y} {D : DSM x} {f : hom x y} → Dec (f ϵ D)
ϵ-dec = is-true-dec

postcomp-closed : ∀ {x} → DSM x → Type (ℓₒ ∪ ℓₘ)
postcomp-closed {x} D =
  ∀ {y z} (f : hom x y) (g : hom y z) → f ϵ D → g ◦ f ϵ D
