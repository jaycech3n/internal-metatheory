{-# OPTIONS --without-K --rewriting #-}

module categories.Categories where

open import categories.Semicategories public

record ᴳᵂCategoryStructure ℓᵢ ℓₒ ℓₘ (G : Type ℓᵢ) (Ob : G → Type ℓₒ)
  : Type (lsuc (ℓᵢ ∪ ℓₒ ∪ ℓₘ)) where
  field ⦃ gwsemicatstr ⦄ : ᴳᵂSemicategoryStructure ℓᵢ ℓₒ ℓₘ G Ob
  open ᴳᵂSemicategoryStructure gwsemicatstr public

  field
    id : ∀ {α} {x : Ob α} → hom x x
    idl : ∀ {α β} {x : Ob α} {y : Ob β} {f : hom x y} → id ◦ f == f
    idr : ∀ {α β} {x : Ob α} {y : Ob β} {f : hom x y} → f ◦ id == f

record ᴳᵂCategory ℓᵢ ℓₒ ℓₘ (G : Type ℓᵢ) : Type (lsuc (ℓᵢ ∪ ℓₒ ∪ ℓₘ)) where
  field
    Ob : G → Type ℓₒ
    gwcatstr : ᴳᵂCategoryStructure ℓᵢ ℓₒ ℓₘ G Ob

  open ᴳᵂCategoryStructure gwcatstr public

ᵂCategoryStructure : ∀ ℓₒ ℓₘ → (Ob : Type ℓₒ) → Type (lsuc (ℓₒ ∪ ℓₘ))
ᵂCategoryStructure ℓₒ ℓₘ Ob = ᴳᵂCategoryStructure lzero ℓₒ ℓₘ ⊤ (λ _ → Ob)
