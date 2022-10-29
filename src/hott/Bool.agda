{-# OPTIONS --without-K #-}

module hott.Bool where

open import hott.Base public

to-Bool : ∀ {ℓ} {A : Type ℓ} → Dec A → Bool
to-Bool (inl _) = true
to-Bool (inr _) = false

is-true : Bool → Type₀
is-true true = ⊤
is-true false = ⊥

module Boolean-Reflection where
  open import hott.Decidable

  ap-to-Bool :
    ∀ {ℓ₁ ℓ₂} {P : Type ℓ₁} {Q : Type ℓ₂}
      (dec-P : Dec P) (dec-Q : Dec Q)
    → (P → Q) → (Q → P)
    → to-Bool dec-P == to-Bool dec-Q
  ap-to-Bool (inl p) (inl q) _ _ = idp
  ap-to-Bool (inl p) (inr ¬q) pq _ = ⊥-rec (¬q (pq p))
  ap-to-Bool (inr ¬p) (inl q) _ qp = ⊥-rec (¬p (qp q))
  ap-to-Bool (inr ¬p) (inr ¬q) _ _ = idp

open Boolean-Reflection public
