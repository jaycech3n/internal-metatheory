{-# OPTIONS --without-K --rewriting #-}

module categories.Semicategories where

open import hott.HoTT public

record WildSemicategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ ∪ ℓₘ))
  where

  infixr 40 _◦_
  field
    hom : Ob → Ob → Type ℓₘ
    _◦_ : ∀ {x y z} → hom y z → hom x y → hom x z
    ass : ∀ {x y z w} {f : hom z w} {g : hom y z} {h : hom x y}
          → (f ◦ g) ◦ h == f ◦ g ◦ h

  dom : ∀ {x y} → hom x y → Ob
  dom {x = x} _ = x

  cod : ∀ {x y} → hom x y → Ob
  cod {y = y} _ = y

  is-initial : Ob → Type (ℓₒ ∪ ℓₘ)
  is-initial x = ∀ y → is-contr (hom x y)

  is-terminal : Ob → Type (ℓₒ ∪ ℓₘ)
  is-terminal x = ∀ y → is-contr (hom y x)

  !ₜₑᵣₘ : ∀ {y} x → is-terminal x → hom y x
  !ₜₑᵣₘ x w = contr-center (w _)

record WildSemicategory ℓₒ ℓₘ : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  field
    Ob : Type ℓₒ
    wildsemicatstr : WildSemicategoryStructure ℓₒ ℓₘ Ob

  open WildSemicategoryStructure wildsemicatstr public
