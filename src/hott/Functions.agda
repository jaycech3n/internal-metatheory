{-# OPTIONS --without-K #-}

module hott.Functions where

open import hott.Base public

private
  variable ℓ ℓ₁ ℓ₂ ℓ₃ : ULevel

λ=₂ : {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (a : A) → B a → Type ℓ}
      {f g : (a : A) (b : B a) → C a b}
      → (∀ a b → f a b == g a b) → f == g
λ=₂ P = λ= (λ= ∘ P)

λ=₃ : {A : Type ℓ₁} {B : Type ℓ₂} {C : A → B → Type ℓ₃} {D : Type ℓ}
      {f g : (a : A) (b : B) → C a b → D}
      → (∀ a b c → f a b c == g a b c) → f == g
λ=₃ P = λ=₂ (λ a b → λ= (P a b))
