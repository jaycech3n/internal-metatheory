{-# OPTIONS --without-K #-}

module cwfs.Contextual where

open import cwfs.CwFs

record ContextualCwFStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ) : Type (lsuc (ℓₒ l⊔ ℓₘ))
  where

  field cwfstr : CwFStructure C
  open CwFStructure cwfstr public

  field
    len : Con → ℕ
    len-O : ∀ {Γ} → (len Γ == O) ≃ (Γ == ◆)
    len-S : ∀ {n} → (Σ[ Γ ∶ Con ] len Γ == 1+ n) ≃ (Σ[ Γ ∶ Con ] Ty Γ × (len Γ == n))

  len-◆ : len ◆ == O
  len-◆ = <– (len-O {◆}) idp


module Contextual-contextual-core {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwf : CwFStructure C)
  where
  open CwFStructure cwf

  listlike : ℕ → Type ℓₒ
  con-of : {n : ℕ} → listlike n → Con

  listlike O = Lift ⊤
  listlike (1+ n) = Σ[ γ ∶ listlike n ] Ty (con-of γ)

  con-of {O} _ = ◆
  con-of {1+ n} (γ , A) = con-of γ ∷ A

  ContextualCon : WildCategory ℓₒ ℓₘ
  WildCategory.Ob ContextualCon = Σ[ n ∶ ℕ ] listlike n
  WildCategory.wildcatstr ContextualCon = record
    { wildsemicatstr = record
        { hom = λ{ (_ , γ) (_ , δ) → Sub (con-of γ) (con-of δ) }
        ; _◦_ = _◦_
        ; ass = ass
        }
    ; id = id
    ; idl = idl
    ; idr = idr }

  cccontextstr : ContextStructure ContextualCon
  cccontextstr = record
    { ◆ = O , lift unit
    ; ◆-terminal = λ{ (_ , γ) → ◆-terminal (con-of γ) } }
  open ContextStructure cccontextstr

  cctytmstr : TyTmStructure ContextualCon
  cctytmstr = record
    { ctxstr = cccontextstr
    ; Ty = λ{ (_ , γ) → Ty (con-of γ) }
    ; _[_] = _[_]
    ; [id] = [id]
    ; [◦] = [◦]
    ; Tm = Tm
    ; _[_]ₜ = _[_]ₜ
    ; [id]ₜ = [id]ₜ
    ; [◦]ₜ = [◦]ₜ }

  cccoeᵀᵐ= :
    {Γ @ (n , γ) : ContextStructure.Con cccontextstr}
    {A A' : Ty (con-of γ)}
    (p : A == A') (t : Tm A)
    → TyTmStructure.coeᵀᵐ cctytmstr {Γ} p t == TyTmStructure.coeᵀᵐ tytmstr p t
  cccoeᵀᵐ= idp t = idp

  ContextualCore : ContextualCwFStructure ContextualCon
  CwFStructure.compstr (ContextualCwFStructure.cwfstr ContextualCore) = record
    { tytmstr = cctytmstr
    ; _∷_ = λ (n , γ) A → 1+ n , γ , A
    ; π = π
    ; υ = υ
    ; _,,_ = _,,_
    ; βπ = βπ
    ; βυ = βυ
    ; η,, = η,,
    ; ,,-◦ = ,,-◦ ∙ ⟨=,, ! (cccoeᵀᵐ= (! [◦]) _) =⟩ }
  ContextualCwFStructure.len ContextualCore = fst
  ContextualCwFStructure.len-O ContextualCore =
    equiv (λ{ idp → idp}) (λ{ idp → idp}) (λ{ idp → idp}) λ{ idp → idp}
  ContextualCwFStructure.len-S ContextualCore = equiv
    (λ{ ((1+ n , γ , A) , idp) → (n , γ) , A , idp })
    (λ{ ((n , γ) , A , idp) → (1+ n , γ , A) , idp })
    (λ{ ((_ , _) , _ , idp) → idp })
    (λ{ ((_ , _ , _) , idp) → idp })
