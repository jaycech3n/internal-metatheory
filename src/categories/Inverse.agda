{-# OPTIONS --without-K --rewriting #-}

module categories.Inverse where

open import categories.Semicategories

record InverseWildSemicategoryStructure {ℓₒ ℓₘ} {Ob : Type ℓₒ}
  (deg : Ob → ℕ)
  (C : WildSemicategoryStructure ℓₒ ℓₘ Ob)
  : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  open WildSemicategoryStructure C

  field hom-inverse : ∀ x y → hom x y → deg y < deg x
