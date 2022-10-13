{-# OPTIONS --without-K #-}

module categories.Inverse where

open import categories.Semicategories

record InverseWildSemicategoryStructure {ℓₒ ℓₘ} {Ob : Type ℓₒ}
  (C : WildSemicategoryStructure ℓₒ ℓₘ Ob)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  open WildSemicategoryStructure C

  field
    deg : Ob → ℕ
    hom-inverse : ∀ x y → hom x y → deg y < deg x
