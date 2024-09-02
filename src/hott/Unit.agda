{-# OPTIONS --without-K --rewriting #-}

module hott.Unit where

open import hott.Base

!⊤ : ∀ {ℓ} {A : Type ℓ} → A → ⊤
!⊤ _ = tt
