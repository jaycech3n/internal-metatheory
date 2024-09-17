{-# OPTIONS --without-K --rewriting #-}

-- Basic structures in precoherent categories with families

module cwfs.Base where

open import categories.Categories public

record ContextStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ) : Type (lsuc (ℓₒ ∪ ℓₘ))
  where

  open WildCategory C renaming (Ob to Con ; hom to Sub) public

  field
    ◆ : Con
    ◆-terminal : is-terminal ◆


record TyTmStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ) : Type (lsuc (ℓₒ ∪ ℓₘ))
  where

  field ctxstr : ContextStructure C
  open ContextStructure ctxstr public

  infixl 40 _[_] _[_]ₜ

  field
    Ty   : Con → Type ℓₒ
    _[_] : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
    [id] : ∀ {Γ} {A : Ty Γ} → A [ id ] == A
    [◦]  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε}
             {A : Ty Ε} -- Greek capital epsilon, \GE
           → A [ g ◦ f ] == A [ g ] [ f ]

    Tm    : ∀ {Γ} → Ty Γ → Type ℓₘ
    _[_]ₜ : ∀ {Γ Δ} {A : Ty Δ} → Tm A → (f : Sub Γ Δ) → Tm (A [ f ])
    [id]ₜ : ∀ {Γ} {A : Ty Γ} {t : Tm A} → t [ id ]ₜ == t [ Tm ↓ [id] ]
    [◦]ₜ  : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm A}
            → t [ g ◦ f ]ₜ == t [ g ]ₜ [ f ]ₜ [ Tm ↓ [◦] ]

  private
    module notation where
      ![◦] : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε}
             → A [ g ] [ f ] == A [ g ◦ f ]
      ![◦] = ! [◦]

      [=_] : ∀ {Γ Δ} {f f' : Sub Γ Δ} {A : Ty Δ}
             → f == f' → A [ f ] == A [ f' ]
      [=_] {A = A} = ap (A [_])

      ap[=] : ∀ {Γ Δ} {f f' : Sub Γ Δ} {A : Ty Δ} (p : f == f')
              → ap Tm [= p ] == ap (Tm ∘ (A [_])) p
      ap[=] idp = idp

      _⁼[_] : ∀ {Γ Δ} {A A' : Ty Δ} (p : A == A') (f : Sub Γ Δ)
              → A [ f ] == A' [ f ]
      p ⁼[ f ] = ap _[ f ] p

      _⁼[_]ₜ : ∀ {Γ Δ} {A : Ty Δ} {a a' : Tm A} (p : a == a') (f : Sub Γ Δ)
              → a [ f ]ₜ == a' [ f ]ₜ
      p ⁼[ f ]ₜ = ap _[ f ]ₜ p

      PathOver-Tm :
        ∀ {Γ} {A A' : Ty Γ} (p : A == A') (t : Tm A) (t' : Tm A') → Type ℓₘ
      PathOver-Tm = PathOver Tm
      syntax PathOver-Tm p t t' = t == t' over⟨ p ⟩

      ![◦]ₜ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm A}
              → t [ g ]ₜ [ f ]ₜ == t [ g ◦ f ]ₜ over⟨ ![◦] ⟩
      ![◦]ₜ = !ᵈ [◦]ₜ

      [=_]ₜ :
        ∀ {Γ Δ} {f f' : Sub Γ Δ} {A : Ty Δ} {t : Tm A} (p : f == f')
        → t [ f ]ₜ == t [ f' ]ₜ over⟨ [= p ] ⟩
      [= idp ]ₜ = idp

      -- Coercing terms to equal terms in equal types
      coeᵀᵐ : ∀ {Γ} {A A' : Ty Γ} → A == A' → Tm A → Tm A'
      coeᵀᵐ p = transp Tm p

      coe!ᵀᵐ : ∀ {Γ} {A A' : Ty Γ} → A == A' → Tm A' → Tm A
      coe!ᵀᵐ p = coeᵀᵐ (! p)

  open notation public

  module ↓ᵀᵐ-notation where
    infixl 30 _↓ᵀᵐ_
    _↓ᵀᵐ_ : ∀ {Γ} {A A' : Ty Γ} → Tm A → A == A' → Tm A'
    t ↓ᵀᵐ p = coeᵀᵐ p t

    test : ∀ {Γ Δ} {σ τ : Sub Γ Δ} {A : Ty Δ} {a : Tm A}
           → (e : σ == τ)
           → ((a [ σ ]ₜ) ↓ᵀᵐ [= e ]) == a [ τ ]ₜ
    test idp = idp


record ComprehensionStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ)
  : Type (lsuc (ℓₒ ∪ ℓₘ)) where

  field tytmstr : TyTmStructure C
  open TyTmStructure tytmstr hiding (ctxstr) public

  infixl 35 _∷_
  infixl 35 _,,_

  field
    _∷_  : (Γ : Con) → Ty Γ → Con
    π    : ∀ {Γ} (A : Ty Γ) → Sub (Γ ∷ A) Γ
    υ    : ∀ {Γ} (A : Ty Γ) → Tm (A [ π A ])
    _,,_ : ∀ {Γ Δ} {A : Ty Δ} (f : Sub Γ Δ) (t : Tm (A [ f ])) → Sub Γ (Δ ∷ A)

    -- The universal property of comprehensions is given by the following β and
    -- η rules.
    βπ : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
         → π A ◦ (f ,, t) == f

    βυ : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
         → υ A [ f ,, t ]ₜ == t over⟨ ! [◦] ∙ [= βπ ] ⟩

    η,, : ∀ {Γ} {A : Ty Γ} → (π A ,, υ A) == id

    ,,-◦ : ∀ {Γ Δ Ε} {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm (A [ g ])}
           → (g ,, t) ◦ f == (g ◦ f ,, coe!ᵀᵐ [◦] (t [ f ]ₜ))
