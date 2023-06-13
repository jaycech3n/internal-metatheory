{-# OPTIONS --without-K --rewriting #-}

module categories.Semicategories where

open import hott.HoTT public

-- ᴳ for "graded", ᵂ for "wild"

record ᴳᵂSemicategoryStructure ℓᵢ ℓₒ ℓₘ (G : Type ℓᵢ) (Ob : G → Type ℓₒ)
  : Type (lsuc (ℓᵢ ∪ ℓₒ ∪ ℓₘ)) where

  infixr 40 _◦_
  field
    hom : ∀ {α β} → Ob α → Ob β → Type ℓₘ
    _◦_ : ∀ {α β γ} {x : Ob α} {y : Ob β} {z : Ob γ} → hom y z → hom x y → hom x z
    ass : ∀ {α β γ δ} {x : Ob α} {y : Ob β} {z : Ob γ} {w : Ob δ}
            {f : hom z w} {g : hom y z} {h : hom x y}
          → (f ◦ g) ◦ h == f ◦ (g ◦ h)

  dom : ∀ {α β} {x : Ob α} {y : Ob β} → hom x y → Ob α
  dom {x = x} _ = x

  cod : ∀ {α β} {x : Ob α} {y : Ob β} → hom x y → Ob β
  cod {y = y} _ = y

  is-initial : ∀ {α} (x : Ob α) → Type _
  is-initial x = ∀ {β} (y : Ob β) → is-contr (hom x y)

  is-terminal : ∀ {α} (x : Ob α) → Type _
  is-terminal x = ∀ {β} (y : Ob β) → is-contr (hom y x)

ᵂSemicategoryStructure : ∀ ℓₒ ℓₘ → (Ob : Type ℓₒ) → Type (lsuc (ℓₒ ∪ ℓₘ))
ᵂSemicategoryStructure ℓₒ ℓₘ Ob = ᴳᵂSemicategoryStructure lzero ℓₒ ℓₘ ⊤ (λ _ → Ob)

record ᵂSemicategory ℓₒ ℓₘ : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  field
    Ob : Type ℓₒ
    wsemicatstr : ᵂSemicategoryStructure ℓₒ ℓₘ Ob

  open ᴳᵂSemicategoryStructure wsemicatstr public
