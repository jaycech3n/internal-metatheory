{-# OPTIONS --without-K --rewriting #-}

open import hott.Base

module hott.Induction where

module _ {ℓ₁ ℓ₂} (A : Type ℓ₁) (_<_ : A → A → Type ℓ₂) where
  data is-accessible : A → Type (ℓ₁ ∪ ℓ₂) where
    acc : ∀ a → (∀ b → b < a → is-accessible b) → is-accessible a

  open is-accessible public

  is-accessible-elim : ∀ {ℓ}
    → (P : (a : A) → is-accessible a → Type ℓ)
    → (f : (a : A)
         → (h : ∀ b → b < a → is-accessible b)
         → (f : ∀ b → (u : b < a) → P b (h b u))
         → P a (acc a h) )
    → (a : A) (c : is-accessible a) → P a c
  is-accessible-elim P f a (acc .a w) =
    f a w (λ b u → is-accessible-elim P f b (w b u))

  is-accessible-rec : ∀ {ℓ}
    → (P : A → Type ℓ)
    → (f : ∀ a → (∀ b → b < a → P b) → P a)
    → ∀ a → is-accessible a → P a
  is-accessible-rec P f = is-accessible-elim (λ a _ → P a) (λ a _ → f a)

  all-accessible : Type (ℓ₁ ∪ ℓ₂)
  all-accessible = (a : A) → is-accessible a

  has-wf-ind : ∀ {ℓ} (P : A → Type ℓ) → Type (ℓ₁ ∪ ℓ₂ ∪ ℓ)
  has-wf-ind P = (∀ a → (∀ b → b < a → P b) → P a) → ∀ a → P a

  all-accessible-implies-has-wf-ind :
    ∀ {ℓ} (P : A → Type ℓ)
    → all-accessible
    → has-wf-ind P
  all-accessible-implies-has-wf-ind P h f a = is-accessible-rec P f a (h a)

module WellFoundedInduction {ℓ₁ ℓ₂}
  (A : Type ℓ₁)
  (_<_ : A → A → Type ℓ₂)
  (c : all-accessible A _<_)
  where

  wf-ind : ∀ {ℓ} (P : A → Type ℓ) → has-wf-ind A _<_ P
  wf-ind P = all-accessible-implies-has-wf-ind A _<_ P c
