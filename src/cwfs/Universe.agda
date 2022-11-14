{-# OPTIONS --without-K #-}

module cwfs.Universe where

open import cwfs.CwFs

record UniverseStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure C)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open CwFStructure cwfstr

  field
    U    : ∀ {Γ} → Ty Γ
    el   : ∀ {Γ} → Tm {Γ} U → Ty Γ
    U[]  : ∀ {Γ Δ} {f : Sub Γ Δ} → U [ f ] == U
    el[] : ∀ {Γ Δ} {f : Sub Γ Δ} {T : Tm {Δ} U}
            → (el T) [ f ] == el (coeᵀᵐ U[] (T [ f ]ₜ))

  private
    module notation where
      _ᵁ : ∀ {Γ Δ} {f : Sub Γ Δ} → Tm (U [ f ]) → Tm U
      _ᵁ = coeᵀᵐ U[]

  open notation
