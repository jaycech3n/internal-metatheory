{-# OPTIONS --without-K #-}

module cwfs.Pi where

open import cwfs.CwFs

record PiStructure {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure C)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open CwFStructure cwfstr

  field
    Π′  : ∀ {Γ} (A : Ty Γ) (B : Ty (Γ ∷ A)) → Ty Γ
    λ′  : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) → Tm (Π′ A B)
    app : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (f : Tm (Π′ A B)) → Tm B

    βΠ′ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) → app (λ′ b) == b
    ηΠ′ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (f : Tm (Π′ A B)) → λ′ (app f) == f

    Π′[]  : ∀ {Γ Δ} {A B} {f : Sub Γ Δ}
            → (Π′ A B) [ f ] == Π′ (A [ f ]) (B [ f ↑ A ])

    λ′[]ₜ : ∀ {Γ Δ} {A B} {f : Sub Γ Δ} {b : Tm B}
            → (λ′ b) [ f ]ₜ == λ′ (b [ f ↑ A ]ₜ) over-Tm⟨ Π′[] ⟩

  private
    module notation where
      infixr 35 _→′_
      _→′_ : ∀ {Γ} (A B : Ty Γ) → Ty Γ
      A →′ B = Π′ A (B [ π A ])

  open notation public

  private
    module definitions where
      _`_ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)}
              (f : Tm (Π′ A B)) (a : Tm A)
            → Tm (B ⟦ a ⟧)
      f ` a = app f ⟦ a ⟧ₜ

      →′[] : ∀ {Γ Δ} {A B : Ty Δ} {f : Sub Γ Δ}
             → (A →′ B) [ f ] == A [ f ] →′ B [ f ]
      →′[] {A = A} {B} {f} =
        (Π′ A (B [ π A ])) [ f ]
          =⟨ Π′[] ⟩
        Π′ (A [ f ]) (B [ π A ] [ f ↑ A ])
          =⟨ ! [◦] ∙ [= ↑-comm ] ∙ [◦]  |in-ctx (Π′ (A [ f ])) ⟩
        Π′ (A [ f ]) (B [ f ] [ π (A [ f ]) ])
          =∎

      appʷ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)}
             → Tm[ Γ ∷ Π′ A B ] ((Π′ A B) ʷ)
             → Tm[ Γ ∷ Π′ A B ∷ A [ π (Π′ A B) ] ] (B [ π (Π′ A B) ↑ A ])
      appʷ t = app $ transp Tm Π′[] t

  open definitions public
