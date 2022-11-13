{-# OPTIONS --without-K #-}

module cwfs.Contextual where

open import cwfs.CwFs

record ContextualCwFStructure {ℓₒ ℓₘ} ℓᵀʸ ℓᵀᵐ (C : WildCategory ℓₒ ℓₘ)
  : Type (lsuc (ℓₒ l⊔ ℓₘ l⊔ ℓᵀʸ l⊔ ℓᵀᵐ)) where

  field cwfstr : CwFStructure ℓᵀʸ ℓᵀᵐ C
  open CwFStructure cwfstr public

  field
    len : Con → ℕ
    len-O : ∀ {Γ} → (len Γ == O) ≃ (Γ == ◆)
    len-S : ∀ {n} → (Σ[ Γ ∶ Con ] len Γ == 1+ n) ≃ (Σ[ Γ ∶ Con ] Ty Γ × (len Γ == n))

  len-◆ : len ◆ == O
  len-◆ = <– (len-O {◆}) idp


module Contextual-contextual-core {ℓₒ ℓₘ ℓᵀʸ ℓᵀᵐ} {C : WildCategory ℓₒ ℓₘ}
  (cwf : CwFStructure ℓᵀʸ ℓᵀᵐ C) where

  open CwFStructure cwf
    renaming
    ( _◦_ to _◦ᶜʷᶠ_
    ; ass to assᶜʷᶠ )

  listlike : ℕ → Type ℓᵀʸ
  con-of : {n : ℕ} → listlike n → Con

  listlike O = Lift ⊤
  listlike (1+ n) = Σ[ γ ∶ listlike n ] Ty (con-of γ)

  con-of {O} _ = ◆
  con-of {1+ n} (γ , A) = con-of γ ∷ A

  ContextualCon : WildCategory ℓᵀʸ ℓₘ
  WildCategory.Ob ContextualCon = Σ[ n ∶ ℕ ] listlike n
  WildCategory.wildcatstr ContextualCon = record
    { wildsemicatstr = record
        { hom = λ{ (_ , γ) (_ , δ) → Sub (con-of γ) (con-of δ) }
        ; _◦_ = _◦ᶜʷᶠ_
        ; ass = assᶜʷᶠ
        }
    ; id = id
    ; idl = idl
    ; idr = idr }

  cctytmstr : TyTmStructure ℓᵀʸ ℓᵀᵐ ContextualCon
  cctytmstr = record
    { ctxstr = record
        { ◆ = (O , lift unit)
        ; ◆-terminal = λ{ (_ , γ) → ◆-terminal (con-of γ) } }
    ; Ty = {!!}
    ; _[_] = {!!}
    ; [id] = {!!}
    ; [◦] = {!!}
    ; Tm = {!!}
    ; _[_]ₜ = {!!}
    ; [id]ₜ = {!!}
    ; [◦]ₜ = {!!} }

  ContextualCore : ContextualCwFStructure ℓᵀʸ ℓᵀᵐ ContextualCon
  CwFStructure.compstr (ContextualCwFStructure.cwfstr ContextualCore) = record
    { tytmstr = {!!}
    ; _∷_ = {!!}
    ; π = {!!}
    ; υ = {!!}
    ; _,,_ = {!!}
    ; βπ = {!!}
    ; βυ = {!!}
    ; η,, = {!!}
    ; ,,-◦ = {!!}
    }

  ContextualCwFStructure.len ContextualCore = {!!}
  ContextualCwFStructure.len-O ContextualCore = {!!}
  ContextualCwFStructure.len-S ContextualCore = {!!}
