\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Termination-Issue-Doc {ℓₘᴵ ℓₒ ℓₘ}
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
Mᵒ : (i b t : ℕ) → shape i b t → Tel (𝔻 (1+ b))

module Diagrams-Abbreviations where
  Mᵒᵗᵒᵗ : (i : ℕ) → Tel (𝔻 i)
  Mᵒᵗᵒᵗ O = •
  Mᵒᵗᵒᵗ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

  Mᵒᶠᵘˡˡ : (i b : ℕ) → Tel (𝔻 (1+ b))
  Mᵒᶠᵘˡˡ i b = Mᵒ i b full shp
    where
    full = hom-size i b
    shp = full-shape i b

  M : (i b t : ℕ) → shape i b t → Con
  M i b t s = close $ Mᵒ i b t s

  𝔸 : (b : ℕ) → Ty (𝔻 b)
  𝔸 b = Πₜₑₗ (Mᵒᵗᵒᵗ b) U

  A : (b : ℕ) → Ty (𝔻 b ∷ 𝔸 b ++ₜₑₗ Mᵒᵗᵒᵗ b [ π (𝔸 b) ]ₜₑₗ)
  A b = generic[ Mᵒᵗᵒᵗ b ]type

open Diagrams-Abbreviations

𝔻 O = ◆
𝔻 (1+ b) = 𝔻 b ∷ 𝔸 b

M⃗ :
  (i b t : ℕ) (s : shape i b t) {j : ℕ} (f : hom i j)
  → let cf = count-factors i b t s f in
    (cfs : shape j b cf)
  → Sub (M i b t s) (M j b cf cfs)

Mᵒ i b (1+ t) s = Mᵒ i b t prev ‣ A b [ idd {!!} ◦ˢᵘᵇ M⃗ i b t prev [t] {!!} ]
  -- Termination problem here:
  -- (M⃗ i b t prev [t] cfps) has type
  --   Sub (M i b t prev) (M b b _ cfps)
  -- which calls
  --   Mᵒ b b (count-factors i b t prev [t]) cfps,
  -- which is not structurally smaller than the arguments to this call.
  -- So try to add an argument to Mᵒ that does decrease.
  where
  prev = prev-shape s
  u = <-from-shape s
  [t] = #[ t ] i b u
  cfps = count-factors-shape i b t prev [t]
Mᵒ i (1+ b) O s = wkₜₑₗ $ Mᵒᶠᵘˡˡ i b -- weakened by 𝔸 (1+ b)
Mᵒ i O O s = •

M⃗ = {!!}

\end{code}
