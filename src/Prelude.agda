{-# OPTIONS --without-K #-}

module Prelude where

open import hott.Base public
open import hott.Paths public
open import hott.PathOver public

-- open import hott.PathOverSeq public

_◅_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} (a : A) (f : (x : A) → B x) → B a
a ◅ f = f a
