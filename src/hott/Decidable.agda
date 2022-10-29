{-# OPTIONS --without-K #-}

module hott.Decidable where

open import hott.Base public

private
  variable ℓ₁ ℓ₂ : ULevel

×-dec : {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → Dec B → Dec (A × B)
×-dec (inl a) (inl b) = inl (a , b)
×-dec (inl a) (inr ¬b) = inr (λ ab → ¬b (snd ab))
×-dec (inr ¬a) _ = inr (λ ab → ¬a (fst ab))

⊔-dec : {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → Dec B → Dec (A ⊔ B)
⊔-dec (inl a) _ = inl (inl a)
⊔-dec (inr ¬a) (inl b) = inl (inr b)
⊔-dec (inr ¬a) (inr ¬b) = inr (λ{(inl a) → ¬a a ; (inr b) → ¬b b})
