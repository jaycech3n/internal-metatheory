{-# OPTIONS --without-K --rewriting #-}

open import cwfs.CwFs

module cwfs.Telescopes {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C) where

open CwFStructure cwfstr

data Tel (Γ : Con) : Type ℓₒ
_++ₜₑₗ_ : (Γ : Con) → Tel Γ → Con

data Tel Γ where
  • : Tel Γ
  _‣_ : (Δ : Tel Γ) → Ty (Γ ++ₜₑₗ Δ) → Tel Γ

Γ ++ₜₑₗ • = Γ
Γ ++ₜₑₗ (Δ ‣ A) = (Γ ++ₜₑₗ Δ) ∷ A

open import cwfs.Pi

module Πₜₑₗ (pistr : PiStructure cwfstr) where
  open PiStructure pistr

  Πₜₑₗ : ∀ {Γ} (Δ : Tel Γ) → Ty (Γ ++ₜₑₗ Δ) → Ty Γ
  Πₜₑₗ • B = B
  Πₜₑₗ (Δ ‣ A) B = Πₜₑₗ Δ (Π′ A B)
