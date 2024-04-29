THE DEFINITION IN THIS FILE DOESN'T FIX TERMINATION, BUT IS FOR DOCUMENTATION
=============================================================================

The partial matching object functor (M, M⃗, M⃗◦) on the cosieve of shape (i, h, t)
is defined in a context 𝔻 k = A₀ : 𝔸₀, ..., Aₖ₋₁ : 𝔸ₖ₋₁.

Nicolai suggests splitting the definition into two parts: depending on whether
h < l-1, or h == l-1.

This makes more explicit the point at which we have to weaken various things,
but does not on its own solve the termination issue, as the partial definition
in this file shows.

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Nicolai {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I
open import reedy.Cosieves I
open Cosieves-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr


𝔻 : ℕ → Con

_<bound_ : ℕ → ℕ → Type₀
h <bound l = 1+ h < l

_=bound_ : ℕ → ℕ → Type₀
h =bound l = 1+ h == l

-- Starred definitions are those defined in the context 𝔻 of "exactly" the right
-- level (i.e. where 𝔻 = A₀ : 𝔸₀, ..., Aₕ : 𝔸ₕ has just the right number of
-- fillers, and no more).
Mᵒ : (l i h t : ℕ) → shape i h t → h <bound l → Tel (𝔻 l)
Mᵒ* : (l i h t : ℕ) → shape i h t → h =bound l → Tel (𝔻 l)

module Diagrams-Abbreviations where
  Mᵒₜₒₜ* : (k : ℕ) → Tel (𝔻 k)
  Mᵒₜₒₜ* O = •
  Mᵒₜₒₜ* (1+ b) = Mᵒ* (1+ b) (1+ b) b (hom-size (1+ b) b) (total-shape-1+ b) idp

  𝔸* : (k : ℕ) → Ty (𝔻 k)
  𝔸* k = Πₜₑₗ (Mᵒₜₒₜ* k) U

  A* : (k : ℕ) → Ty (𝔻 k ∷ 𝔸* k ++ₜₑₗ Mᵒₜₒₜ* k [ π (𝔸* k) ]ₜₑₗ)
  A* k = generic[ Mᵒₜₒₜ* k ]type

open Diagrams-Abbreviations

𝔻 O = ◆
𝔻 (1+ b) = 𝔻 b ∷ 𝔸* b

M⃗ :
  ∀ l i h t s w {j} (f : hom i j)
  → let cf = count-factors i h t s f in
    (cfs : shape j h cf)
  → Sub (close $ Mᵒ l i h t s w) (close $ Mᵒ l j h cf cfs w)

M⃗* :
  ∀ l i h t s p {j} (f : hom i j)
  → let cf = count-factors i h t s f in
    (cfs : shape j h cf)
  → Sub (close $ Mᵒ* l i h t s p) (close $ Mᵒ* l j h cf cfs p)


Mᵒ (1+ O) i h t s (ltSR ())
Mᵒ (2+ b) i .b t s ltS = wkₜₑₗ $ Mᵒ* (1+ b) i b t s idp
Mᵒ (2+ b) i h t s (ltSR w) = wkₜₑₗ $ Mᵒ (1+ b) i h t s w
-- Mᵒ (2+ b) i h t w s = {!!}

Mᵒ* (1+ O) i .O O s idp = •
Mᵒ* (1+ O) i .O (1+ t) s idp =
  let Mᵒ*-prev = Mᵒ* (1+ O) i O t (prev-shape s) idp
   in Mᵒ*-prev ‣ A* O [ πₜₑₗ Mᵒ*-prev ]

Mᵒ* (2+ b) i (1+ .b) O s idp =
  wkₜₑₗ $ Mᵒ* (1+ b) i b (hom-size i b) (full-shape i b) idp
Mᵒ* (2+ b) i (1+ .b) (1+ t) s idp =
  Mᵒ* (2+ b) i (1+ b) t prev idp
    ‣ A* (1+ b) [ idd {!!} ◦ˢᵘᵇ M⃗* (2+ b) i (1+ b) t prev idp [t] cfps ]
  where
  prev = prev-shape s
  u = <-from-shape s
  [t] = #[ t ] i (1+ b) u
  cfps = count-factors-shape i (1+ b) t prev [t]

M⃗ (1+ O) i h t s (ltSR ())
M⃗ (2+ b) i h t s w f cfs = {!!}

M⃗* (1+ O) i h t s p f cfs = {!!}
M⃗* (2+ b) i h t s p f cfs = {!!}

\end{code}
