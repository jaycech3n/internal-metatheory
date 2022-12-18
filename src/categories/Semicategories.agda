{-# OPTIONS --without-K --rewriting #-}

module categories.Semicategories where

open import hott.HoTT public

record WildSemicategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  infixr 40 _◦_
  field
    hom : Ob → Ob → Type ℓₘ
    _◦_ : ∀ {x y z} → hom y z → hom x y → hom x z
    ass : ∀ {x y z w} {f : hom z w} {g : hom y z} {h : hom x y}
          → (f ◦ g) ◦ h == f ◦ (g ◦ h)

  dom : ∀ {x y} → hom x y → Ob
  dom {x} _ = x

  cod : ∀ {x y} → hom x y → Ob
  cod {y = y} _ = y

  is-initial : (x : Ob) → Type (ℓₒ l⊔ ℓₘ)
  is-initial x = (y : Ob) → is-contr (hom x y)

  is-terminal : (x : Ob) → Type (ℓₒ l⊔ ℓₘ)
  is-terminal x = (y : Ob) → is-contr (hom y x)

record PreSemicategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field ⦃ wildsemicatstr ⦄ : WildSemicategoryStructure ℓₒ ℓₘ Ob
  open WildSemicategoryStructure wildsemicatstr public

  field hom-is-set : ∀ {x y} → is-set (hom x y)

record StrictSemicategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field ⦃ presemicatstr ⦄ : PreSemicategoryStructure ℓₒ ℓₘ Ob
  open PreSemicategoryStructure presemicatstr public

  field Ob-is-set : is-set Ob

record WildSemicategory ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field
    Ob : Type ℓₒ
    wildsemicatstr : WildSemicategoryStructure ℓₒ ℓₘ Ob

  open WildSemicategoryStructure wildsemicatstr public

record PreSemicategory ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field
    Ob : Type ℓₒ
    presemicatstr : PreSemicategoryStructure ℓₒ ℓₘ Ob

record StrictSemicategory ℓₒ ℓₘ : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  field
    Ob : Type ℓₒ
    strictsemicatstr : StrictSemicategoryStructure ℓₒ ℓₘ Ob
