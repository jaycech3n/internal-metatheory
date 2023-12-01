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

  private
    module IdArrows where
      idd : ∀ {x y} → x == y → hom x y
      idd idp = id

      iddl : ∀ {x y z} (p : y == z) (σ : hom x y)
             → idd p ◦ σ == transp (hom x) p σ
      iddl idp σ = idl

      iddr : ∀ {x y z} (p : x == y) (σ : hom y z)
             → σ ◦ idd p == transp! (λ x → hom x z) p σ
      iddr idp σ = idr

  open IdArrows public

record WildCategory ℓₒ ℓₘ : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  field
    Ob : Type ℓₒ
    wildcatstr : WildCategoryStructure ℓₒ ℓₘ Ob

  open WildCategoryStructure wildcatstr public
