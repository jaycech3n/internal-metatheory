{-# OPTIONS --without-K --rewriting #-}

module cwfs.contextual.Sigma where

open import cwfs.contextual.CwFs

record SigmaStructure {ℓₒ ℓₘ} (ccwf : ContextualCwF ℓₒ ℓₘ) : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open ContextualCwF ccwf

  field
    Σ′   : ∀ {n} {Γ : Con n} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    _﹐_ : ∀ {n} {Γ : Con n} {A} {B : Ty (Γ ∷ A)} (a : Tm A) (b : Tm (B ⟦ a ⟧))
           → Tm (Σ′ A B)
    fst′ : ∀ {n} {Γ : Con n} {A} {B : Ty (Γ ∷ A)} → Tm (Σ′ A B) → Tm A
    snd′ : ∀ {n} {Γ : Con n} {A} {B : Ty (Γ ∷ A)} (ab : Tm (Σ′ A B))
           → Tm (B ⟦ fst′ ab ⟧)

    ﹐-fst′ : ∀ {n} {Γ : Con n} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B ⟦ a ⟧)}
              → fst′ (a ﹐ b) == a

    ﹐-snd′ : ∀ {n} {Γ : Con n} {A} {B : Ty (Γ ∷ A)} {a : Tm A} {b : Tm (B ⟦ a ⟧)}
              → snd′ (a ﹐ b) == b over-Tm⟨ ﹐-fst′ |in-ctx (B ⟦_⟧) ⟩

    ηΣ′ : ∀ {n} {Γ : Con n} {A} {B : Ty (Γ ∷ A)} {ab : Tm (Σ′ A B)}
          → (fst′ ab ﹐ snd′ ab) == ab

    Σ′[] : ∀ {m n} {Γ : Con m} {Δ : Con n} {A B} {f : Sub Γ Δ}
           → (Σ′ A B) [ f ] == Σ′ (A [ f ]) (B [ f ↑ A ])

    ﹐[]ₜ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A B}
             {f : Sub Γ Δ} {a : Tm A} {b : Tm (B ⟦ a ⟧)}
            → (a ﹐ b) [ f ]ₜ == (a [ f ]ₜ ﹐ coe!ᵀᵐ ([]-⟦⟧ B f a) (b [ f ]ₜ)) over-Tm⟨ Σ′[] ⟩

  private
    module notation where
      infixl 35 _×′_
      _×′_ : ∀ {n} {Γ : Con n} (A B : Ty Γ) → Ty Γ
      A ×′ B = Σ′ A (B [ π A ])

  open notation public
