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

  is-iso : {x y : Ob} (f : hom x y) → Type ℓₘ
  is-iso {x} {y} f = Σ[ g ∶ hom y x ] (g ◦ f == id) × (f ◦ g == id)

  infix 30 _≅_
  _≅_ : (x y : Ob) → Type ℓₘ
  x ≅ y = Σ[ f ∶ hom x y ] is-iso f

  id-to-iso : ∀ x y → x == y → x ≅ y
  id-to-iso x .x idp = id , id , idl , idr

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
