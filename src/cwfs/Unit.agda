{-# OPTIONS --without-K #-}

module cwfs.Unit where

open import cwfs.CwFs

record UnitStructure {ℓₒ ℓₘ ℓᵀʸ ℓᵀᵐ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure ℓᵀʸ ℓᵀᵐ C)
  : Type (lsuc (ℓₒ l⊔ ℓₘ l⊔ ℓᵀʸ l⊔ ℓᵀᵐ)) where

  open CwFStructure cwfstr

  field
    ⊤′   : ∀ {Γ} → Ty Γ
    *′   : ∀ {Γ} → Tm {Γ} ⊤′
    η⊤′  : ∀ {Γ} {t : Tm {Γ} ⊤′} → t == *′
    ⊤′[] : ∀ {Γ Δ} {f : Sub Γ Δ} → ⊤′ [ f ] == ⊤′
