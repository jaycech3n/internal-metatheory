{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import cwfs.CwFs

module cwfs.Telescopes {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C) where

open CwFStructure cwfstr

{- Small inductive-recursive definition of telescopes Θ in internal contexts Γ,
and context extension by telescopes -}

data Tel (Γ : Con) : Type ℓₒ
_++ₜₑₗ_ : (Γ : Con) → Tel Γ → Con

infixl 30 _++ₜₑₗ_
infixl 35 _‣_

data Tel Γ where
  • : Tel Γ
  _‣_ : (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ) → Tel Γ

Γ ++ₜₑₗ • = Γ
Γ ++ₜₑₗ (Θ ‣ A) = (Γ ++ₜₑₗ Θ) ∷ A

close : {Γ : Con} → Tel Γ → Con
close {Γ} Θ = Γ ++ₜₑₗ Θ

{- Substitution in telescopes

Consider a telescope Θ = (Δ ⊢ A₁, A₂, ..., Aₙ) in context Δ. For any
substitution f : Sub Γ Δ we get the telescope Θ[f]ₜₑₗ given by the left hand
column of the diagram

                 ⋮                            ⋮
                 ↡                             ↡
      Γ ∷ A₁[f] ∷ A₂[f ∷ₛ A₁] ------------> Δ ∷ A₁ ∷ A₂
                 |         f ∷ₛ A₁ ∷ₛ A₂         |
                 ↡                             ↡
           Γ ∷ A₁[f] ----------------------> Δ ∷ A₁
                 |           f ∷ₛ A₁            |
                 ↡                             ↡
                 Γ --------------------------> Δ
                               f

(see cwfs.CwFs for the definition of _∷ₛ_).
-}

infixl 40 _[_]ₜₑₗ _++ₛ_

_[_]ₜₑₗ : ∀ {Γ Δ} → Tel Δ → Sub Γ Δ → Tel Γ
_++ₛ_ : ∀ {Γ Δ} (f : Sub Γ Δ) (Θ : Tel Δ) → Sub (Γ ++ₜₑₗ Θ [ f ]ₜₑₗ) (Δ ++ₜₑₗ Θ)

• [ f ]ₜₑₗ = •
(Θ ‣ A) [ f ]ₜₑₗ = Θ [ f ]ₜₑₗ ‣ A [ f ++ₛ Θ ]

f ++ₛ • = f
f ++ₛ (Θ ‣ A) = f ++ₛ Θ ∷ₛ A

private
  module sanity-check
    (Γ Δ : Con) (f : Sub Γ Δ)
    (A₁ : Ty Δ) (A₂ : Ty (Δ ∷ A₁)) (A₃ : Ty (Δ ∷ A₁ ∷ A₂))
    where
    Θ = • ‣ A₁ ‣ A₂ ‣ A₃

    _ : Θ [ f ]ₜₑₗ == • ‣ A₁ [ f ] ‣ A₂ [ f ∷ₛ A₁ ] ‣ A₃ [ f ∷ₛ A₁ ∷ₛ A₂ ]
    _ = idp

-- Projection
πₜₑₗ : ∀ {Γ} (Θ : Tel Γ) → Sub (Γ ++ₜₑₗ Θ) Γ
πₜₑₗ • = id
πₜₑₗ (Θ ‣ A) = πₜₑₗ Θ ◦ π A

{- The following diagram commutes:

                    σ ++ₛ Θ
          Γ ++ Θ[σ] ------> Δ ++ Θ
    π (Θ[σ]) |                | π Θ
             ↓                ↓
             Γ -------------> Δ
                      σ
-}
++ₛ-comm : ∀ {Γ Δ} (σ : Sub Γ Δ) (Θ : Tel Δ)
  → πₜₑₗ Θ ◦ (σ ++ₛ Θ) == σ ◦ πₜₑₗ (Θ [ σ ]ₜₑₗ)
++ₛ-comm σ • = idl ∙ ! idr
++ₛ-comm σ (Θ ‣ A) =
  (πₜₑₗ Θ ◦ π A) ◦ (σ ++ₛ Θ ∷ₛ A)
    =⟨ ass ⟩
  πₜₑₗ Θ ◦ (π A ◦ (σ ++ₛ Θ ∷ₛ A))
    =⟨ βπ |in-ctx (πₜₑₗ Θ ◦_) ⟩
  πₜₑₗ Θ ◦ (σ ++ₛ Θ) ◦ π (A [ σ ++ₛ Θ ])
    =⟨ ! ass ∙ (++ₛ-comm σ Θ |in-ctx (_◦ π _)) ∙ ass ⟩
  σ ◦ πₜₑₗ (Θ [ σ ]ₜₑₗ) ◦ π (A [ σ ++ₛ Θ ])
    =∎

-- Weaken a *telescope* by a type
infix 32 wknₜₑₗ_by
wknₜₑₗ_by : ∀ {Γ} → Tel Γ → (X : Ty Γ) → Tel (Γ ∷ X)
wknₜₑₗ Θ by X = Θ [ π X ]ₜₑₗ

wkₜₑₗ : ∀ {Γ} {X : Ty Γ} → Tel Γ → Tel (Γ ∷ X)
wkₜₑₗ {X = X} Θ = wknₜₑₗ Θ by X

-- Weakening by a telescope
infix 37 wkn_byₜₑₗ
wkn_byₜₑₗ : ∀ {Γ} → Ty Γ → (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ)
wkn X byₜₑₗ Θ = X [ πₜₑₗ Θ ]

wknₜ_byₜₑₗ : ∀ {Γ} {X : Ty Γ} (x : Tm X) (Θ : Tel Γ) → Tm (wkn X byₜₑₗ Θ)
wknₜ x byₜₑₗ Θ = x [ πₜₑₗ Θ ]ₜ

-- A particular version of a weakened variable υ that we need.
υ⁺ : ∀ {Γ} (Θ : Tel Γ) (X : Ty Γ) → Tm (X [ πₜₑₗ Θ ◦ (π X ++ₛ Θ) ])
υ⁺ Θ X = coeᵀᵐ p (υ X [ πₜₑₗ (Θ [ π X ]ₜₑₗ) ]ₜ)
  where
  p : X [ π X ] [ πₜₑₗ (wknₜₑₗ Θ by X) ] == X [ πₜₑₗ Θ ◦ (π X ++ₛ Θ) ]
  p = ![◦] ∙ [= ! (++ₛ-comm (π X) Θ)]

wkn-sub-lemma :
  ∀ {Γ} (Θ Θ' : Tel Γ) (X : Ty Γ)
  → (σ : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ'))
  → πₜₑₗ Θ' ◦ σ == πₜₑₗ Θ
  → Σ (Sub (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ) (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ'))
    λ σ↑X → (π X ++ₛ Θ') ◦ σ↑X == σ ◦ (π X ++ₛ Θ)
wkn-sub-lemma = {!!}

wkn-sub :
  ∀ {Γ} (Θ Θ' : Tel Γ) (σ : Sub (Γ ++ₜₑₗ Θ) (Γ ++ₜₑₗ Θ'))
  → πₜₑₗ Θ' ◦ σ == πₜₑₗ Θ
  → (X : Ty Γ)
  → Sub (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ) (Γ ∷ X ++ₜₑₗ wkₜₑₗ Θ')
wkn-sub Θ Θ' σ p X = fst (wkn-sub-lemma Θ Θ' X σ p)

{-
-- Weaken a *substitution* between telescopes by a type
wkn-sub-lemma : ∀ {Γ Δ} (Θ : Tel Γ) (X : Ty Δ) (σ₀ : Sub Γ Δ)
  (Θ' : Tel Δ)
  (σ : Sub (Γ ++ₜₑₗ Θ) (Δ ++ₜₑₗ Θ'))
  → πₜₑₗ Θ' ◦ σ == σ₀ ◦ πₜₑₗ Θ
  → Σ (Sub (Γ ∷ X [ σ₀ ] ++ₜₑₗ wkₜₑₗ Θ) (Δ ∷ X ++ₜₑₗ wkₜₑₗ Θ'))
    λ σ↑X → (π X ++ₛ Θ') ◦ σ↑X == σ ◦ (π (X [ σ₀ ]) ++ₛ Θ)

wkn-sub-lemma Θ X σ₀ • σ p =
  (σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ,, coeᵀᵐ q (υ⁺ Θ (X [ σ₀ ])))
  , βπ
  where
  σ-σ₀ : σ == σ₀ ◦ πₜₑₗ Θ
  σ-σ₀ = ! idl ∙ p

  q : X [ σ₀ ] [ πₜₑₗ Θ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ]
      == X [ σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ]
  q = ![◦] ∙ [= ! ass ∙ ap (_◦ (π (X [ σ₀ ]) ++ₛ Θ)) (! σ-σ₀) ]

wkn-sub-lemma {Γ} {Δ} Θ X σ₀ (Θ' ‣ A) σ p =
  σ↑X , comm
  where
  -- Notation
  π++Θ = π (X [ σ₀ ]) ++ₛ Θ
  π++Θ' = π X ++ₛ Θ'
  π++Θ'‣A = π X ++ₛ (Θ' ‣ A)

  πσ-σ₀ : πₜₑₗ Θ' ◦ π A ◦ σ == σ₀ ◦ πₜₑₗ Θ
  πσ-σ₀ = ! ass ∙ p

  rec = wkn-sub-lemma Θ X σ₀ Θ' (π A ◦ σ) πσ-σ₀
  πσ↑X = fst rec

  πσ↑X-comm : π++Θ' ◦ πσ↑X == (π A ◦ σ) ◦ π++Θ
  πσ↑X-comm = snd rec

  botleft = σ ◦ π++Θ

  q : A ʷ [ botleft ] == A [ π++Θ' ] [ πσ↑X ]
  q = ![◦] ∙ ! [= ass ] ∙ ! [= πσ↑X-comm ] ∙ [◦]

  σ↑X = (πσ↑X ,, coeᵀᵐ q (υ A [ botleft ]ₜ))

  topright = π++Θ'‣A ◦ σ↑X

  comm : topright == botleft
  comm =
    topright

      =⟨ idp ⟩

    ( π++Θ' ◦ π _ ,, coeᵀᵐ ![◦] (υ _) ) ◦ σ↑X

      =⟨ ,,-◦ ⟩

    ( (π++Θ' ◦ π _) ◦ σ↑X ,,
      coeᵀᵐ ![◦] (coeᵀᵐ ![◦] (υ _) [ σ↑X ]ₜ) )

      =⟨ ⟨=,, coeᵀᵐ[]ₜ ![◦] (υ _) σ↑X |in-ctx (coeᵀᵐ ![◦]) =⟩ ⟩

    ( (π++Θ' ◦ π _) ◦ σ↑X ,,
      coeᵀᵐ ![◦] (coeᵀᵐ (ap (_[ σ↑X ]) ![◦]) (υ _ [ σ↑X ]ₜ)) )

      =⟨ ⟨=,, {!!} =⟩ ⟩

    ( (π++Θ' ◦ π _) ◦ σ↑X ,,
      coeᵀᵐ ![◦] (coeᵀᵐ (ap (_[ σ↑X ]) ![◦]) (coeᵀᵐ ([= ! βπ ] ∙ [◦]) (coeᵀᵐ q
        (υ _ [ botleft ]ₜ)))) )

      =⟨ ⟨= ass ,,=⟩ ⟩
    ( π++Θ' ◦ π _ ◦ σ↑X ,, _ )
      =⟨ ⟨= βπ |in-ctx (π++Θ' ◦_) ,,=⟩ ⟩
    ( π++Θ' ◦ πσ↑X ,, _ )
      =⟨ ⟨= πσ↑X-comm ,,=⟩ ⟩
    ( (π A ◦ σ) ◦ π++Θ ,, _ )
      =⟨ ⟨= ass ,,=⟩ ⟩
    ( π A ◦ botleft ,, _ )
      =⟨ ⟨=,, {!!} =⟩ ⟩
    ( π A ◦ botleft ,, coe!ᵀᵐ [◦] (υ A [ botleft ]ₜ) )
      =⟨ ! (η-sub botleft) ⟩
    botleft
      =∎

wkn-sub : ∀ {Γ Δ} (Θ : Tel Γ) (X : Ty Δ) (σ₀ : Sub Γ Δ)
  (Θ' : Tel Δ)
  (σ : Sub (Γ ++ₜₑₗ Θ) (Δ ++ₜₑₗ Θ'))
  → πₜₑₗ Θ' ◦ σ == σ₀ ◦ πₜₑₗ Θ
  → Sub (Γ ∷ X [ σ₀ ] ++ₜₑₗ wkₜₑₗ Θ) (Δ ∷ X ++ₜₑₗ wkₜₑₗ Θ')
wkn-sub {Γ} {Δ} Θ X σ₀ Θ' σ p = fst (wkn-sub-lemma {Γ} {Δ} Θ X σ₀ Θ' σ p)
-}


-- Internal Π types from telescopes
open import cwfs.Pi
module Πₜₑₗ (pistr : PiStructure cwfstr) where
  open PiStructure pistr

  Πₜₑₗ : ∀ {Γ} (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ) → Ty Γ
  Πₜₑₗ • B = B
  Πₜₑₗ (Θ ‣ A) B = Πₜₑₗ Θ (Π′ A B)

  Πₜₑₗ[] :
    ∀ {Γ Δ} (Θ : Tel Δ) (B : Ty (Δ ++ₜₑₗ Θ)) (f : Sub Γ Δ)
    → (Πₜₑₗ Θ B) [ f ] == Πₜₑₗ (Θ [ f ]ₜₑₗ) (B [ f ++ₛ Θ ])
  Πₜₑₗ[] • B f = idp
  Πₜₑₗ[] (Θ ‣ A) B f = Πₜₑₗ[] Θ (Π′ A B) f ∙ ap (Πₜₑₗ (Θ [ f ]ₜₑₗ)) Π′[]

  appₜₑₗ : ∀ {Γ} (Θ : Tel Γ) {B : Ty (Γ ++ₜₑₗ Θ)} → Tm (Πₜₑₗ Θ B) → Tm B
  appₜₑₗ • f = f
  appₜₑₗ (Θ ‣ A) f = app (appₜₑₗ Θ f)

  λₜₑₗ : ∀ {Γ} (Θ : Tel Γ) {B : Ty (Γ ++ₜₑₗ Θ)} → Tm B → Tm (Πₜₑₗ Θ B)
  λₜₑₗ • b = b
  λₜₑₗ (Θ ‣ A) b = λₜₑₗ Θ (λ′ b)

  λₜₑₗappₜₑₗ : ∀ {Γ} Θ {B : Ty (Γ ++ₜₑₗ Θ)} f → λₜₑₗ Θ {B} (appₜₑₗ Θ {B} f) == f
  λₜₑₗappₜₑₗ • f = idp
  λₜₑₗappₜₑₗ (Θ ‣ A) f = ap (λₜₑₗ Θ) (ηΠ′ _) ∙ λₜₑₗappₜₑₗ Θ f

  appₜₑₗλₜₑₗ : ∀ {Γ} Θ {B : Ty (Γ ++ₜₑₗ Θ)} b → appₜₑₗ Θ {B} (λₜₑₗ Θ b) == b
  appₜₑₗλₜₑₗ • b = idp
  appₜₑₗλₜₑₗ (Θ ‣ A) b = ap app (appₜₑₗλₜₑₗ Θ _) ∙ βΠ′ b

  Tm-Πₜₑₗ-equiv : ∀ {Γ} (Θ : Tel Γ) (B : Ty (Γ ++ₜₑₗ Θ)) → Tm (Πₜₑₗ Θ B) ≃ Tm B
  Tm-Πₜₑₗ-equiv Θ B = equiv (appₜₑₗ Θ) (λₜₑₗ Θ) (appₜₑₗλₜₑₗ Θ) (λₜₑₗappₜₑₗ Θ)

  open import cwfs.Universe
  module TelIndexedTypes (univstr : UniverseStructure cwfstr) where
    open UniverseStructure univstr

    generic[_]type :
      ∀ {Γ} (Θ : Tel Γ)
      → let X = Πₜₑₗ Θ U in
        Ty (Γ ∷ X ++ₜₑₗ Θ [ π X ]ₜₑₗ)
    generic[ Θ ]type = el $ appₜₑₗ (Θ [ π X ]ₜₑₗ) $ transp Tm p (υ X)
      where
      X = Πₜₑₗ Θ U

      p : X [ π X ] == Πₜₑₗ (Θ [ π X ]ₜₑₗ) U
      p = Πₜₑₗ[] Θ U (π X) ∙ ap (Πₜₑₗ (Θ [ π X ]ₜₑₗ)) U[]
