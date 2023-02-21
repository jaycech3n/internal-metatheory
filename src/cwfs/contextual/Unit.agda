{-# OPTIONS --without-K --rewriting #-}

module cwfs.contextual.Unit where

open import cwfs.contextual.CwFs

record UnitStructure {ℓₒ ℓₘ} (ccwf : ContextualCwF ℓₒ ℓₘ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open ContextualCwF ccwf

  field
    ⊤′   : ∀ {n} {Γ : Con n} → Ty Γ
    *′   : ∀ {n} {Γ : Con n} → Tm {Γ = Γ} ⊤′
    η⊤′  : ∀ {n} {Γ : Con n} {t : Tm {Γ = Γ} ⊤′} → t == *′
    ⊤′[] : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} → ⊤′ [ f ] == ⊤′
