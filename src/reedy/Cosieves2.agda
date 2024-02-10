{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.Cosieves2 {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I

open import categories.DSM (SimpleSemicategory.wildsemicatstr I)

CoSv : (i : ℕ) → Type ℓₘ
CoSv i = Σ (DSM i) postcomp-closed

infix 999 _̇  _ᵒ

_̇  : ∀ {i} → CoSv i → DSM i
T ̇  = fst T

_ᵒ : ∀ {i} (T : CoSv i) → postcomp-closed (T ̇ )
T ᵒ = snd T

·-postcomp-closed :
  ∀ {i j} (T : CoSv i) (f : hom i j)
  → postcomp-closed ⦅(λ g → g ◦ f ∋ T ̇ )⦆
·-postcomp-closed T f g h w =
  (T ᵒ) (g ◦ f) h w
  ◂$ transp! (is-true ∘ ((T ̇ ) _)) ass

_·_ : ∀ {i j} → CoSv i → hom i j → CoSv j
T · f = ⦅(λ g → g ◦ f ∋ T ̇ )⦆ , ·-postcomp-closed T f

record Height {i} (T : CoSv i) : Type ℓₘ where
  field
    height : ℕ
    witness : hom i height
    none-above : ∀ j → height < j → (f : hom i j) → f ϵ/ T ̇

open Height

height-of : ∀ {i} (T : CoSv i) → Height T
height-of T = record { height = {!!} ; witness = {!!} ; none-above = {!!} }
-- Okay this is doable, but lengthy. Let's keep using the shapes presentation
-- for now.

record is-linear {i} (T : CoSv i) : Type ℓₘ where
  field
    width : ℕ
    shape : width ≤ hom-size i (height (height-of T))
    -- <-height : ∀ j → j < h → (f : hom i j) → f ϵ T ̇
    -- >-height : ∀ j → h < j → (f : hom i j) → f ϵ/ T ̇
    -- <-width : ∀ k (u : k < t) → #[ k ] i h (<-≤-< u shape) ϵ T ̇
    -- ≥-width : ∀ k → t ≤ k → (u : k < hom-size i h) → #[ k ] i h u ϵ/ T ̇

·-preserves-linearity :
  ∀ {i j} (T : CoSv i) (f : hom i j)
  → is-linear T → is-linear (T · f)
·-preserves-linearity T f L = {!!}
