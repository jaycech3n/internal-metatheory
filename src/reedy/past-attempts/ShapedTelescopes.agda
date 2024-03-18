{-# OPTIONS --without-K --rewriting #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs

module reedy.ShapedTelescopes {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  where

open SuitableSemicategory I
open import reedy.LinearSieves I

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open import cwfs.Telescopes cwfstr

data Tel_[_,_,_] : (Γ : Con) (i h t : ℕ) → shape i h t → Type ℓₒ
tel : ∀ {Γ} {i h t} {sh} → Tel Γ [ i , h , t ] sh → Tel Γ

infixl 35 _‣_ _↑ₛₜₑₗ_

data Tel_[_,_,_] where
  • :
    ∀ {Γ} {i} {sh : shape i O O}
    → Tel Γ [ i , O , O ] sh
  _‣_ :
    ∀ {Γ} {i h t} {sh : shape i h (1+ t)}
      (Θ : Tel Γ [ i , h , t ] (shapeₜ↓ sh))
      (A : Ty (Γ ++ₜₑₗ tel Θ))
    → Tel Γ [ i , h , 1+ t ] sh
  _↑ₛₜₑₗ_ :
    ∀ {Γ} {i h} {sh : shape i (1+ h) O}
      (Θ : Tel Γ [ i , h , hom-size i h ] (shapeₕ↓ sh))
      (X : Ty Γ)
    → Tel (Γ ∷ X) [ i , 1+ h , O ] sh

tel • = •
tel (Θ ‣ A) = tel Θ ‣ A
tel (Θ ↑ₛₜₑₗ X) = wknₜₑₗ tel Θ by X

-- Here we just reexport functions on telescopes, but lifted to shaped
-- telescopes.

infixl 30 _++ₛₜₑₗ_
_++ₛₜₑₗ_ : ∀ {i h t} {sh} (Γ : Con) → Tel Γ [ i , h , t ] sh → Con
_++ₛₜₑₗ_ Γ = _++ₜₑₗ_ Γ ∘ tel

infix 37 wkn_byₛₜₑₗ
wkn_byₛₜₑₗ : ∀ {Γ} {i h t} {sh}
  → Ty Γ → (Θ : Tel Γ [ i , h , t ] sh) → Ty (Γ ++ₛₜₑₗ Θ)
wkn X byₛₜₑₗ = wkn X byₜₑₗ ∘ tel

open import cwfs.Pi
module Πₛₜₑₗ (pistr : PiStructure cwfstr) where
  open Πₜₑₗ pistr

  Πₛₜₑₗ : ∀ {Γ} {i h t} {sh}
    → (Θ : Tel Γ [ i , h , t ] sh) → Ty (Γ ++ₛₜₑₗ Θ) → Ty Γ
  Πₛₜₑₗ Θ B = Πₜₑₗ (tel Θ) B

  Πₛₜₑₗ-[]-comm :
    ∀ {Γ Δ} {i h t} {sh}
      (Θ : Tel Δ [ i , h , t ] sh) (B : Ty (Δ ++ₛₜₑₗ Θ)) (f : Sub Γ Δ)
    → (Πₛₜₑₗ Θ B) [ f ] == Πₜₑₗ ((tel Θ) [ f ]ₜₑₗ) (B [ f ↑ₜₑₗ tel Θ ])
  Πₛₜₑₗ-[]-comm Θ B f = Πₜₑₗ-[]-comm (tel Θ) B f

  appₛₜₑₗ : ∀ {Γ} {i h t} {sh}
    (Θ : Tel Γ [ i , h , t ] sh) {B : Ty (Γ ++ₛₜₑₗ Θ)} → Tm (Πₛₜₑₗ Θ B) → Tm B
  appₛₜₑₗ Θ f = appₜₑₗ (tel Θ) f

module projection
  (Γ : ℕ → Con)
  (X : (n : ℕ) → Ty (Γ n))
  (P : ∀ n → Γ n ∷ X n == Γ (1+ n))
  where
  proj[_,1+_,_] : (i h t : ℕ) {sh : shape i (1+ h) (1+ t)}
    → (j k : ℕ) (ssh : shape (1+ h) j k)
    → (Θ : Tel Γ (1+ h) [ i , 1+ h , t ] (shapeₜ↓ sh))
    → Σ[ Θ' ː Tel Γ j [ 1+ h , j , k ] ssh ]
        Sub (Γ (1+ h) ++ₛₜₑₗ Θ) (Γ j ++ₛₜₑₗ Θ')
  proj[ i ,1+ h , t ] j (1+ k) ssh Θ = {!!}
  proj[ i ,1+ h , t ] {sh} (1+ j) O ssh Θ =
    let
    rec-tel , rec-sub =
      proj[ i ,1+ h , t ] {sh} j (hom-size (1+ h) j) (shapeₕ↓ ssh) Θ
    X , p = P j
    in transp (λ ◻ → Tel ◻ [ 1+ h , 1+ j , O ] ssh) p (rec-tel ↑ₛₜₑₗ X) , {!!}
  proj[ i ,1+ h , t ] O O ssh Θ = • , {!!}
