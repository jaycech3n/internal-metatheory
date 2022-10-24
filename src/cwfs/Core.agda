{-# OPTIONS --without-K #-}

-- Basic structures in categories with families, ignoring coherence conditions
module cwfs.Core where

open import categories.Categories public

record ContextStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where

  open WildCategory C renaming (Ob to Con ; hom to Sub) public

  field
    ◆ : Con
    ◆-terminal : is-terminal ◆


record TyTmStructure {ℓₒ ℓₘ} ℓᵀʸ ℓᵀᵐ (C : WildCategory ℓₒ ℓₘ)
  : Type (lsuc (ℓₒ l⊔ ℓₘ l⊔ ℓᵀʸ l⊔ ℓᵀᵐ)) where

  field ctxstr : ContextStructure C
  open ContextStructure ctxstr public

  infixl 40 _[_] _[_]ₜ

  field
    Ty   : Con → Type ℓᵀʸ
    _[_] : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    [id] : ∀ {Γ} {A : Ty Γ} → A [ id ] == A
    [◦]  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} -- Greek capital epsilon, \GE
           → A [ g ◦ f ] == A [ g ] [ f ]

    Tm    : ∀ {Γ} → Ty Γ → Type ℓᵀᵐ
    _[_]ₜ : ∀ {Γ Δ} {A : Ty Δ} → Tm A → (f : Sub Γ Δ) → Tm (A [ f ])
    [id]ₜ : ∀ {Γ} {A : Ty Γ} {t : Tm A} → t [ id ]ₜ == t [ Tm ↓ [id] ]
    [◦]ₜ  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm A}
            → t [ g ◦ f ]ₜ == t [ g ]ₜ [ f ]ₜ [ Tm ↓ [◦] ]

  private
    module definitions where
      PathOver-Tm : ∀ {Γ} {A A' : Ty Γ} (p : A == A') (t : Tm A) (t' : Tm A') → Type ℓᵀᵐ
      PathOver-Tm = PathOver Tm
      syntax PathOver-Tm p t t' = t == t' over-Tm⟨ p ⟩

      [=_] : ∀ {Γ Δ} {f f' : Sub Γ Δ} {A : Ty Δ}
             → f == f' → A [ f ] == A [ f' ]
      [=_] {A = A} = ap (A [_])

      [=_]ₜ : ∀ {Γ Δ} {f f' : Sub Γ Δ} {A : Ty Δ} {t : Tm A} (p : f == f')
              → t [ f ]ₜ == t [ f' ]ₜ over-Tm⟨ [= p ] ⟩
      [= idp ]ₜ = idp

      -- Coercing terms to equal terms in equal types
      coeᵀᵐ : ∀ {Γ} {A A' : Ty Γ} → A == A' → Tm A → Tm A'
      coeᵀᵐ {A = A} idp = idf (Tm A)

      coe!ᵀᵐ : ∀ {Γ} {A A' : Ty Γ} → A == A' → Tm A' → Tm A
      coe!ᵀᵐ p = coeᵀᵐ (! p)

  open definitions public


record ComprehensionStructure {ℓₒ ℓₘ} ℓᵀʸ ℓᵀᵐ (C : WildCategory ℓₒ ℓₘ)
  : Type (lsuc (ℓₒ l⊔ ℓₘ l⊔ ℓᵀʸ l⊔ ℓᵀᵐ)) where

  field tytmstr : TyTmStructure ℓᵀʸ ℓᵀᵐ C
  open TyTmStructure tytmstr public

  infixl 20 _∷_
  infixl 30 _,,_

  field
    _∷_  : (Γ : Con) → Ty Γ → Con
    π    : ∀ {Γ} (A : Ty Γ) → Sub (Γ ∷ A) Γ
    υ    : ∀ {Γ} (A : Ty Γ) → Tm (A [ π A ])
    _,,_ : ∀ {Γ Δ} {A : Ty Δ} (f : Sub Γ Δ) (t : Tm (A [ f ])) → Sub Γ (Δ ∷ A)

    -- The universal property of comprehensions is given by the following β and η rules.
    βπ : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
         → π A ◦ (f ,, t) == f

    βυ : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
         → υ A [ f ,, t ]ₜ == t over-Tm⟨ ! [◦] ∙ [= βπ ] ⟩

    η,, : ∀ {Γ} {A : Ty Γ} → (π A ,, υ A) == id

    ,,-◦ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm (A [ g ])}
           → (g ,, t) ◦ f == (g ◦ f ,, coe!ᵀᵐ [◦] (t [ f ]ₜ))
