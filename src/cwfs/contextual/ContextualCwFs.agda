{-# OPTIONS --without-K #-}

module cwfs.contextual.ContextualCwFs where

open import categories.Categories public

-- This is meant to be a (bundled) indexed version of cwfs.Contextual
record ContextualCwF {ℓₒ ℓₘ} : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  infixl 20 _∷_
  infixl 30 _,,_
  infixr 40 _◦_
  infixl 40 _[_] _[_]ₜ
  field
    -- Category of contexts with length
    Con : ℕ → Type ℓₒ
    Sub : ∀ {m n} → Con m → Con n → Type ℓₘ
    _◦_ : ∀ {k m n} {Γ : Con m} {Δ : Con n} {Ε : Con k}
          → Sub Δ Ε → Sub Γ Δ → Sub Γ Ε
    ass : ∀ {m n k l} {Γ : Con m} {Δ : Con n} {Ε : Con k} {Ζ : Con l}
          {f : Sub Ε Ζ} {g : Sub Δ Ε} {h : Sub Γ Δ}
          → (f ◦ g) ◦ h == f ◦ (g ◦ h)
    id  : ∀ {n} {Γ : Con n} → Sub Γ Γ
    idl : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} → id ◦ f == f
    idr : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} → f ◦ id == f

    -- Empty context
    ◆ : Con O
    ◆-terminal : ∀ {n} (Γ : Con n) → is-contr (Sub Γ ◆)

    -- Types, terms, substitution
    Ty   : ∀ {n} → Con n → Type ℓₒ
    _[_] : ∀ {m n} {Γ : Con m} {Δ : Con n} → Ty Δ → Sub Γ Δ → Ty Γ
    [id] : ∀ {n} {Γ : Con n} {A : Ty Γ} → A [ id ] == A
    [◦]  : ∀ {m n k} {Γ : Con m} {Δ : Con n} {Ε : Con k}
           {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} -- Greek capital epsilon, \GE
           → A [ g ◦ f ] == A [ g ] [ f ]

    Tm    : ∀ {n} {Γ : Con n} → Ty Γ → Type ℓₘ
    _[_]ₜ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A : Ty Δ}
            → Tm A → (f : Sub Γ Δ) → Tm (A [ f ])
    [id]ₜ : ∀ {n} {Γ : Con n} {A : Ty Γ} {t : Tm A}
            → t [ id ]ₜ == t [ Tm ↓ [id] ]
    [◦]ₜ  : ∀ {m n k} {Γ : Con m} {Δ : Con n} {Ε : Con k}
            {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm A}
            → t [ g ◦ f ]ₜ == t [ g ]ₜ [ f ]ₜ [ Tm ↓ [◦] ]

    -- Comprehension
    _∷_  : ∀ {n} (Γ : Con n) → Ty Γ → Con (1+ n)
    π    : ∀ {n} {Γ : Con n} (A : Ty Γ) → Sub (Γ ∷ A) Γ
    υ    : ∀ {n} {Γ : Con n} (A : Ty Γ) → Tm (A [ π A ])
    _,,_ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A : Ty Δ}
           → (f : Sub Γ Δ) (t : Tm (A [ f ])) → Sub Γ (Δ ∷ A)

    βπ : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ}
         {A : Ty Δ} {t : Tm (A [ f ])}
         → π A ◦ (f ,, t) == f

    βυ : ∀ {m n} {Γ : Con m} {Δ : Con n}
         {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
         → υ A [ f ,, t ]ₜ == t [ Tm ↓ ! [◦] ∙ ap (A [_]) βπ ]

    η,, : ∀ {n} {Γ : Con n} {A : Ty Γ} → (π A ,, υ A) == id

    ,,-◦ : ∀ {m n k} {Γ : Con m} {Δ : Con n} {Ε : Con k}
           {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm (A [ g ])}
           → (g ,, t) ◦ f == (g ◦ f ,, transp Tm (! [◦]) (t [ f ]ₜ))

    -- Contextuality
    Con-O : is-contr (Con O)
      -- cf. comment on ContextualStructure.len-◆-equiv in cwfs.Contextual
    Con-S : ∀ {n} → is-equiv (uncurry (_∷_ {n}))
