{-# OPTIONS --without-K #-}

module categories.Categories where

open import categories.Semicategories public

record WildCategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field ⦃ wildsemicatstr ⦄ : WildSemicategoryStructure ℓₒ ℓₘ Ob
  open WildSemicategoryStructure wildsemicatstr public

  field
    id : ∀ {x} → hom x x
    idl : ∀ {x y} {f : hom x y} → id ◦ f == f
    idr : ∀ {x y} {f : hom x y} → f ◦ id == f

record WildCategory ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field
    Ob  : Type ℓₒ
    wildcatstr : WildCategoryStructure ℓₒ ℓₘ Ob
  open WildCategoryStructure wildcatstr public

  module isomorphisms where
    record is-iso  {x y : Ob} (f : hom x y) : Type (ℓₒ l⊔ ℓₘ) where
      field
        g : hom y x
        g◦f : g ◦ f == id
        f◦g : f ◦ g == id

    infix 30 _≅_
    record _≅_ (x y : Ob) : Type (ℓₒ l⊔ ℓₘ) where
      field
        f : hom x y
        f-is-iso : is-iso f

    id-to-iso : ∀ x y → x == y → x ≅ y
    id-to-iso x .x idp = record
      { f = id
      ; f-is-iso = record { g = id ; g◦f = idl ; f◦g = idl } }

  open isomorphisms public

record PreCategory ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field ⦃ C ⦄ : WildCategory ℓₒ ℓₘ
  open WildCategory C public

  field
    Hom-is-set : ∀ {x y} → is-set (hom x y)

record StrictCategory ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field ⦃ C ⦄ : PreCategory ℓₒ ℓₘ
  open PreCategory C hiding (C) public

  field
    Ob-is-set  : is-set Ob

-- Univalent category
record Category ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field ⦃ C ⦄ : PreCategory ℓₒ ℓₘ
  open PreCategory C hiding (C) public
  field
    id-to-iso-is-equiv : (x y : Ob) → is-equiv (id-to-iso x y)
