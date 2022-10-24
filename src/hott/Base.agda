{-# OPTIONS --without-K #-}

module hott.Base where

open import HoTT
  renaming
  ( lsucc          to lsuc
  ; lmax           to _l⊔_
  ; transport      to transp
  ; [_]            to ∣_∣
  ; ℕ-has-dec-eq   to _≟-ℕ_
  ; Fin-has-dec-eq to _≟-Fin_
  ; <-dec          to _<?_
  ; ≤-dec          to _≤?_
  ) public

infixl 1 _◅_
_◅_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} (a : A) (f : (x : A) → B x) → B a
a ◅ f = f a

to-Bool : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false
