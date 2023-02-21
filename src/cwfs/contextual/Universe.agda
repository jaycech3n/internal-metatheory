{-# OPTIONS --without-K --rewriting #-}

module cwfs.contextual.Universe where

open import cwfs.contextual.CwFs

record UniverseStructure {ℓₒ ℓₘ} (ccwf : ContextualCwF ℓₒ ℓₘ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open ContextualCwF ccwf

  field
    U    : ∀ {n} {Γ : Con n} → Ty Γ
    el   : ∀ {n} {Γ : Con n} → Tm {Γ = Γ} U → Ty Γ
    U[]  : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} → U [ f ] == U
    el[] : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} {T : Tm {Γ = Δ} U}
           → (el T) [ f ] == el (coeᵀᵐ U[] (T [ f ]ₜ))

  private
    module notation where
      _ᵁ : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} → Tm (U [ f ]) → Tm U
      _ᵁ = coeᵀᵐ U[]

  open notation
