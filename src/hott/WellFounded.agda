{-# OPTIONS --safe #-}

-- Wellfoundedness, the usual stuff. (todo: better documentation)

module hott.WellFounded where

open import Agda.Primitive

module _ {ℓ ℓ'} {A : Set ℓ} (_<_ : A → A → Set ℓ') where

  data Acc (x : A) : Set (ℓ ⊔ ℓ') where
    acc : (∀ y → y < x → Acc y) → Acc x

  is-wf : Set (ℓ ⊔ ℓ')
  is-wf = ∀ x → Acc x

  module _ {ℓ''} {P : A → Set ℓ''} where

    -- accessibility induction
    acc-ind : ∀ x → Acc x → (∀ x → (∀ y → y < x → P y) → P x) → P x
    acc-ind x (acc p) ih = ih x λ y y<x → acc-ind y (p y y<x) ih

    -- wellfounded induction
    wfi : is-wf → (∀ x → (∀ y → y < x → P y) → P x) → ∀ x → P x
    wfi wf ih x = acc-ind x (wf x) ih
