{-# OPTIONS --without-K --rewriting #-}

module cwfs.contextual.Pi where

open import cwfs.contextual.CwFs

record PiStructure {ℓₒ ℓₘ} (ccwf : ContextualCwF ℓₒ ℓₘ) : Type (lsuc (ℓₒ ∪ ℓₘ)) where

  open ContextualCwF ccwf

  field
    Π̇ : ∀ {n} {Γ : Con n} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    λ̇ : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)}
        → (b : Tm B) → Tm (Π̇  A B)
    app : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)}
          → (f : Tm (Π̇ A B)) → Tm B

    βΠ̇ : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)}
          → (b : Tm B) → app (λ̇ b) == b
    ηΠ̇ : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)}
          → (f : Tm (Π̇ A B)) → λ̇ (app f) == f

    Π[]  : ∀ {m n} {Γ : Con m} {Δ : Con n} {A B} {f : Sub Γ Δ}
            → (Π̇ A B) [ f ] == Π̇ (A [ f ]) (B [ f ↑ A ])

    λ̇[]ₜ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A B} {f : Sub Γ Δ} {b : Tm B}
            → (λ̇ b) [ f ]ₜ == λ̇ (b [ f ↑ A ]ₜ) over-Tm⟨ Π[] ⟩

  private
    module notation where
      infixr 35 _→̇_
      _→̇_ : ∀ {n} {Γ : Con n} (A B : Ty Γ) → Ty Γ
      A →̇ B = Π̇ A (B [ π A ])

  open notation public

  private
    module definitions where
      _`_ : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)}
              (f : Tm (Π̇ A B)) (a : Tm A)
            → Tm (B ⟦ a ⟧)
      f ` a = app f ⟦ a ⟧ₜ

      →̇[] : ∀ {m n} {Γ : Con m} {Δ : Con n} {A B : Ty Δ} {f : Sub Γ Δ}
             → (A →̇ B) [ f ] == A [ f ] →̇ B [ f ]
      →̇[] {A = A} {B} {f} =
        (Π̇ A (B [ π A ])) [ f ]
          =⟨ Π[] ⟩
        Π̇ (A [ f ]) (B [ π A ] [ f ↑ A ])
          =⟨ ! [◦] ∙ [= ↑-comm ] ∙ [◦]  |in-ctx (Π̇ (A [ f ])) ⟩
        Π̇ (A [ f ]) (B [ f ] [ π (A [ f ]) ])
          =∎

      appʷ : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)}
             → Tm[ Γ ∷ Π̇ A B ] ((Π̇ A B) ʷ)
             → Tm[ Γ ∷ Π̇ A B ∷ A [ π (Π̇ A B) ] ] (B [ π (Π̇ A B) ↑ A ])
      appʷ t = app $ transp Tm Π[] t

  open definitions public
