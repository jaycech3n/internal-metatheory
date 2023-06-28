{-# OPTIONS --without-K --rewriting #-}

module cwfs.Unit where

open import cwfs.CwFs

record UnitStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure C)
  : Type (lsuc (ℓₒ ∪ ℓₘ)) where

  open CwFStructure cwfstr

  field
    ⊤′   : ∀ {Γ} → Ty Γ
    *′   : ∀ {Γ} → Tm {Γ} ⊤′
    η⊤′  : ∀ {Γ} {t : Tm {Γ} ⊤′} → t == *′
    ⊤′[] : ∀ {Γ Δ} {f : Sub Γ Δ} → ⊤′ [ f ] == ⊤′
