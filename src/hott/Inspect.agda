{-# OPTIONS --without-K --rewriting #-}

module hott.Inspect where

open import hott.Base public

-- Copied from the Agda standard library
record Equate_·_and_ {ℓ₁ ℓ₂}
  {A : Type ℓ₁} {B : A → Type ℓ₂}
  (f : (x : A) → B x) (x : A) (y : B x)
  : Type (ℓ₁ ∪ ℓ₂) where
  constructor have
  field p : f x == y

inspect : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
            (f : (x : A) → B x) (x : A)
          → Equate f · x and f x
inspect f x = have idp
