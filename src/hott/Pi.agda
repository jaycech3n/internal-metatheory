{-# OPTIONS --without-K #-}

module hott.Pi where

open import hott.Base public

private
  module equivalences {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (e : A ≃ B) where
    fwd-transp-Π-dom : {P : B → Type ℓ₃} → ((b : B) → P b) → (a : A) → P (–> e a)
    fwd-transp-Π-dom f = f ∘ –> e

    bwd-transp-Π-dom : {P : A → Type ℓ₃} → ((a : A) → P a) → (b : B) → P (<– e b)
    bwd-transp-Π-dom f = f ∘ <– e

open equivalences public
