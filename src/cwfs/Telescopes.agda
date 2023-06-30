{-# OPTIONS --without-K --rewriting #-}

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

{- Substitution in telescopes

Consider a telescope Θ = (Δ ⊢ A₁, A₂, ..., Aₙ) in context Δ. For any
substitution f : Sub Γ Δ we get the telescope Θ[f]ₜₑₗ given by the left hand
column of the diagram

                 ⋮                            ⋮
                 ↡                             ↡
      Γ ∷ A₁[f] ∷ A₂[f ↑ A₁] ------------> Δ ∷ A₁ ∷ A₂
                 |         f ↑ A₁ ↑ A₂         |
                 ↡                             ↡
           Γ ∷ A₁[f] ----------------------> Δ ∷ A₁
                 |           f ↑ A₁            |
                 ↡                             ↡
                 Γ --------------------------> Δ
                               f

(see cwfs.CwFs for the definition of _↑_).
-}

infixl 40 _[_]ₜₑₗ _↑ₜₑₗ_

_[_]ₜₑₗ : ∀ {Γ Δ} → Tel Δ → Sub Γ Δ → Tel Γ
_↑ₜₑₗ_ : ∀ {Γ Δ} (f : Sub Γ Δ) (Θ : Tel Δ) → Sub (Γ ++ₜₑₗ Θ [ f ]ₜₑₗ) (Δ ++ₜₑₗ Θ)

• [ f ]ₜₑₗ = •
(Θ ‣ A) [ f ]ₜₑₗ = Θ [ f ]ₜₑₗ ‣ A [ f ↑ₜₑₗ Θ ]

f ↑ₜₑₗ • = f
f ↑ₜₑₗ (Θ ‣ A) = f ↑ₜₑₗ Θ ↑ A

private
  module sanity-check
    (Γ Δ : Con) (f : Sub Γ Δ)
    (A₁ : Ty Δ) (A₂ : Ty (Δ ∷ A₁)) (A₃ : Ty (Δ ∷ A₁ ∷ A₂))
    where
    Θ = • ‣ A₁ ‣ A₂ ‣ A₃

    _ : Θ [ f ]ₜₑₗ == • ‣ A₁ [ f ] ‣ A₂ [ f ↑ A₁ ] ‣ A₃ [ f ↑ A₁ ↑ A₂ ]
    _ = idp

-- Weaken a *telescope* by a type
infix 32 wknₜₑₗ_by
wknₜₑₗ_by : ∀ {Γ} → Tel Γ → (X : Ty Γ) → Tel (Γ ∷ X)
wknₜₑₗ Θ by X = Θ [ π X ]ₜₑₗ

-- Weaken a *type* by a telescope
infix 37 wkn_by
wkn_by : ∀ {Γ} → Ty Γ → (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ)
wkn X by • = X
wkn X by (Θ ‣ A) = (wkn X by Θ) [ π A ]

-- Internal Π types from telescopes
open import cwfs.Pi
module Πₜₑₗ (pistr : PiStructure cwfstr) where
  open PiStructure pistr

  Πₜₑₗ : ∀ {Γ} (Θ : Tel Γ) → Ty (Γ ++ₜₑₗ Θ) → Ty Γ
  Πₜₑₗ • B = B
  Πₜₑₗ (Θ ‣ A) B = Πₜₑₗ Θ (Π′ A B)

  Πₜₑₗ-[]-comm :
    ∀ {Γ Δ} {Θ : Tel Δ} (B : Ty (Δ ++ₜₑₗ Θ)) (f : Sub Γ Δ)
    → (Πₜₑₗ Θ B) [ f ] == Πₜₑₗ (Θ [ f ]ₜₑₗ) (B [ f ↑ₜₑₗ Θ ])
  Πₜₑₗ-[]-comm {Θ = •} B f = {!idp!}
  Πₜₑₗ-[]-comm {Θ = Θ ‣ A} B f = {!!}
