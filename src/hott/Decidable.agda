{-# OPTIONS --without-K --rewriting #-}

module hott.Decidable where

open import hott.Base public
open import hott.Bool public

private
  variable ℓ ℓ₁ ℓ₂ : ULevel

×-dec : {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → Dec B → Dec (A × B)
×-dec (inl a) (inl b) = inl (a , b)
×-dec (inl a) (inr ¬b) = inr (λ ab → ¬b (snd ab))
×-dec (inr ¬a) _ = inr (λ ab → ¬a (fst ab))

⊔-dec : {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → Dec B → Dec (A ⊔ B)
⊔-dec (inl a) _ = inl (inl a)
⊔-dec (inr ¬a) (inl b) = inl (inr b)
⊔-dec (inr ¬a) (inr ¬b) = inr (λ{(inl a) → ¬a a ; (inr b) → ¬b b})

ap-to-Bool :
  ∀ {ℓ₁ ℓ₂} {P : Type ℓ₁} {Q : Type ℓ₂}
    (dec-P : Dec P) (dec-Q : Dec Q)
  → (P → Q) → (Q → P)
  → to-Bool dec-P == to-Bool dec-Q
ap-to-Bool (inl p) (inl q) _ _ = idp
ap-to-Bool (inl p) (inr ¬q) pq _ = ⊥-rec (¬q (pq p))
ap-to-Bool (inr ¬p) (inl q) _ qp = ⊥-rec (¬p (qp q))
ap-to-Bool (inr ¬p) (inr ¬q) _ _ = idp

-- Reflection and erasure

⌞_⌟ : {A : Type ℓ} → Dec A → Bool
⌞ inl a ⌟ = true
⌞ inr ¬a ⌟ = false

⌜_⌝ : {A : Type ℓ} {D : Dec A} → is-true ⌞ D ⌟ → A
⌜_⌝ {D = inl a} _ = a

True : {A : Type ℓ} → Dec A → Type₀
True D = is-true ⌞ D ⌟

by : {A : Type ℓ} {D : Dec A} → A → True D
by {D = inl a} a' = tt
by {D = inr ¬a} a = ⊥-rec (¬a a)

-- Reasoning

contrapos : {A : Type ℓ₁} {B : Type ℓ₂} → Dec A → Dec B → (¬ B → ¬ A) → A → B
contrapos decA (inl b) c a = b
contrapos decA (inr ¬b) c a = ⊥-rec $  c ¬b a
