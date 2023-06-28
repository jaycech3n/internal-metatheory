{-# OPTIONS --without-K --rewriting #-}

module categories.Categories where

open import categories.Semicategories public

record WildCategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  field ⦃ wildsemicatstr ⦄ : WildSemicategoryStructure ℓₒ ℓₘ Ob
  open WildSemicategoryStructure wildsemicatstr public

  field
    id : ∀ {x} → hom x x
    idl : ∀ {x y} {f : hom x y} → id ◦ f == f
    idr : ∀ {x y} {f : hom x y} → f ◦ id == f

record WildCategory ℓₒ ℓₘ : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  field
    Ob : Type ℓₒ
    wildcatstr : WildCategoryStructure ℓₒ ℓₘ Ob

  open WildCategoryStructure wildcatstr public
