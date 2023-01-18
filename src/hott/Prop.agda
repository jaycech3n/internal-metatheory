{-# OPTIONS --without-K --rewriting #-}

module hott.Prop where

open import hott.Base public

coe-Prop :
  ∀ {ℓ₁ ℓ₂} {P : Type ℓ₁}
  → is-prop P
  → (B : P → Type ℓ₂)
  → ∀ {x y} → B x → B y
coe-Prop p B {x} {y} b = transp B (prop-path p x y) b
