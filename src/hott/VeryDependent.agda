{-# OPTIONS --without-K --rewriting #-}

module hott.VeryDependent where

open import hott.HoTT

Fiber : ∀ {ℓ} → Type (lsuc ℓ)
Fiber {ℓ} = Σ[ B ﹕ Type ℓ ] B

SequentialType : ∀ {ℓ} → Type ℓ → Type (lsuc ℓ)
SequentialType {ℓ} A = A → Fiber

module _ {ℓ₁ ℓ₂}
  (A : Type ℓ₁) (_<_ : A → A → Type ℓ₂) (<-acc : all-acc A _<_)
  where

  open WellFoundedInduction A _<_ <-acc

  F : SequentialType A
  F = wf-ind (λ _ → Fiber) {!!}
    where
    
