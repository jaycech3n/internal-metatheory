{-# OPTIONS --without-K #-}

module hott.Bool where

open import hott.Base public

to-Bool : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false

is-true : Bool → Type₀
is-true true = ⊤
is-true false = ⊥
