{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

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

                    σ ++ Θ
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
υ⁺ Θ X = coeᵀᵐ p (υ X [ πₜₑₗ (Θ [ π _ ]ₜₑₗ) ]ₜ)
  where
  p : X [ π X ] [ πₜₑₗ (wknₜₑₗ Θ by X) ] == X [ πₜₑₗ Θ ◦ (π X ++ₛ Θ) ]
  p = ![◦] ∙ [= ! (++ₛ-comm (π X) Θ)]

-- Weaken a *substitution* between telescopes by a type
module _ {Γ Δ} (X : Ty Δ) (Θ : Tel Γ) where
  wkn-sub :
    (Θ' : Tel Δ) (σ : Sub (Γ ++ₜₑₗ Θ) (Δ ++ₜₑₗ Θ'))
    (σ₀ : Sub Γ Δ) (p : πₜₑₗ Θ' ◦ σ == σ₀ ◦ πₜₑₗ Θ)
    → Sub (Γ ∷ X [ σ₀ ] ++ₜₑₗ wkₜₑₗ Θ) (Δ ∷ X ++ₜₑₗ wkₜₑₗ Θ')

  wkn-sub-comm :
    (Θ' : Tel Δ) (σ : Sub (Γ ++ₜₑₗ Θ) (Δ ++ₜₑₗ Θ'))
    (σ₀ : Sub Γ Δ) (p : πₜₑₗ Θ' ◦ σ == σ₀ ◦ πₜₑₗ Θ)
    → (π X ++ₛ Θ') ◦ wkn-sub Θ' σ σ₀ p == σ ◦ (π _ ++ₛ Θ)

  wkn-sub • σ σ₀ p = σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ,, coeᵀᵐ q (υ⁺ Θ (X [ σ₀ ]))
    where
    p' : σ₀ ◦ πₜₑₗ Θ == σ
    p' = ! p ∙ idl

    q : X [ σ₀ ] [ πₜₑₗ Θ ◦ (π _ ++ₛ Θ) ] == X [ σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ]
    q = ![◦] ∙ [= ! ass ∙ ap (_◦ (π _ ++ₛ Θ)) p' ]

  wkn-sub (Θ' ‣ A) σ σ₀ p =
    wkn-sub Θ' (π A ◦ σ) σ₀ p' ,, coeᵀᵐ q (υ A [ σ ◦ (π _ ++ₛ Θ) ]ₜ)
    where
    p' : πₜₑₗ Θ' ◦ π A ◦ σ == σ₀ ◦ πₜₑₗ Θ
    p' = ! ass ∙ p

    q : A ʷ [ σ ◦ (π (X [ σ₀ ]) ++ₛ Θ) ]
        == A [ π X ++ₛ Θ' ] [ wkn-sub Θ' (π A ◦ σ) σ₀ p' ]
    q =
      A ʷ [ σ ◦ (π _ ++ₛ Θ) ]
        =⟨ ![◦] ∙ [= ! ass ] ⟩
      A [ (π A ◦ σ) ◦ (π _ ++ₛ Θ) ]
        =⟨ ! [= wkn-sub-comm Θ' (π _ ◦ σ) σ₀ (! ass ∙ p) ] ∙ [◦] ⟩
      A [ π X ++ₛ Θ' ] [ wkn-sub Θ' (π A ◦ σ) σ₀ p' ]
        =∎

  wkn-sub-comm • σ σ₀ p = βπ
  wkn-sub-comm (Θ' ‣ A) σ σ₀ p = sub= _ _ π◦= {!!}
    where
    p' = ! ass ∙ p
    wkn-sub-rec = wkn-sub Θ' (π A ◦ σ) σ₀ p'

    wkn-sub-comm-rec :
      (π X ++ₛ Θ') ◦ wkn-sub-rec == π A ◦ σ ◦ (π (X [ σ₀ ]) ++ₛ Θ)
    wkn-sub-comm-rec = wkn-sub-comm Θ' (π A ◦ σ) σ₀ p' ∙ ass

    topright = (π X ++ₛ Θ' ∷ₛ A) ◦ wkn-sub (Θ' ‣ A) σ σ₀ p
    botleft = σ ◦ (π (X [ σ₀ ]) ++ₛ Θ)

    π◦= : π A ◦ topright == π A ◦ botleft
    π◦= =
      {!π A ◦ topright
        =⟨ ! ass  ⟩
      (π A ◦ (π X ++ₛ Θ' ∷ₛ A)) ◦ wkn-sub _ σ σ₀ p
        =⟨ ? ⟩
      π A ◦ botleft
        =∎!}

-- Internal Π types from telescopes
open import cwfs.Pi
module Πₜₑₗ (pistr : PiStructure cwfstr) where
  open PiStructure pistr

  Πₜₑₗ : ∀ {Γ} (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ) → Ty Γ
  Πₜₑₗ • B = B
  Πₜₑₗ (Θ ‣ A) B = Πₜₑₗ Θ (Π′ A B)

  Πₜₑₗ-[]-comm :
    ∀ {Γ Δ} (Θ : Tel Δ) (B : Ty (Δ ++ₜₑₗ Θ)) (f : Sub Γ Δ)
    → (Πₜₑₗ Θ B) [ f ] == Πₜₑₗ (Θ [ f ]ₜₑₗ) (B [ f ++ₛ Θ ])
  Πₜₑₗ-[]-comm • B f = idp
  Πₜₑₗ-[]-comm (Θ ‣ A) B f =
    Πₜₑₗ-[]-comm Θ (Π′ A B) f ∙ ap (Πₜₑₗ (Θ [ f ]ₜₑₗ)) Π′[]

  appₜₑₗ : ∀ {Γ} (Θ : Tel Γ) {B : Ty (Γ ++ₜₑₗ Θ)} → Tm (Πₜₑₗ Θ B) → Tm B
  appₜₑₗ • f = f
  appₜₑₗ (Θ ‣ A) f = app (appₜₑₗ Θ f)
