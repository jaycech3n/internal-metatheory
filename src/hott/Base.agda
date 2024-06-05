{-# OPTIONS --without-K --rewriting #-}

module hott.Base where

open import HoTT
  hiding
  ( if_then_else_
  ; Pullback
  ; _∙ₛ_ )
  renaming
  ( lsucc          to lsuc
  ; lmax           to _∪_
  ; transport      to transp
  ; [_]            to ∣_∣
  ; ℕ-has-dec-eq   to _≟-ℕ_
  ; Fin-has-dec-eq to _≟-Fin_
  ; <-dec          to _<?_
  ; ≤-dec          to _≤?_
  ) public

infixl 1 _◂$_
_◂$_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} (a : A) (f : (x : A) → B x) → B a
a ◂$ f = f a

✶ : ∀ {ℓ} → Lift {j = ℓ} ⊤
✶ = lift unit

-- Notation for readability
show_by_ : ∀ {ℓ} (A : Type ℓ) → A → A
show A by a = a

:⟨_⟩_ = show_by_

infixr 1 show_by_ :⟨_⟩_
