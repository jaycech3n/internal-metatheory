{-# OPTIONS --without-K #-}

module hott.Conditionals where

open import hott.Base public

case : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
       → A ⊔ B → (A → C) → (B → C) → C
case a⊔b a b = ⊔-rec a b a⊔b

if : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → (A → B) → (¬ A → B) → B
if = case
