{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams2 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I
open import reedy.Cosieves I
open Cosieves-IsStrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

𝔻 : ℕ → Con
Mᵒ : (n i h t : ℕ) → shape i h t → i ≤ n → Tel (𝔻 (1+ h))

M : (i h t : ℕ) → shape i h t → Con
M i h t s = close (Mᵒ i i h t s lteE)

-- Experiment:
-- pᴹ : (t : ℕ) {h : ℕ} {s : shape h h t} {s' : shape h h 0}
--   → Sub (M h h t s) (M h h 0 s')

Mᵒₜₒₜ : (i : ℕ) → Tel (𝔻 i)
Mᵒₜₒₜ 0 = •
Mᵒₜₒₜ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

𝔸 : (i : ℕ) → Ty (𝔻 i)
𝔸 i = Πₜₑₗ (Mᵒₜₒₜ i) U

A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒₜₒₜ i [ π (𝔸 i) ]ₜₑₗ)
A i = generic[ Mᵒₜₒₜ i ]type

𝔻 0 = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f
        sh = count-factors-gives-shape i h t s f
    in Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ i h t s) (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ j h cf sh) -- somehow indicate here that j < i?

Mᵒ i h (1+ t) s = Mᵒ i h t shp ‣ A h [ {!!} ◦ˢᵘᵇ {!M⃗ i h t shp (#[ t ] i h u)!} ]
  where
  shp = prev-shape s
  u : t < hom-size i h
  u = S≤-< s
Mᵒ i (1+ h) O s = Mᵒ i h full shp [ π (𝔸 (1+ h)) ]ₜₑₗ
  where
  full = hom-size i h
  shp = full-shape i h
Mᵒ i O O s = •

-- Experiment:
pᴹ O {O} = id
pᴹ O {1+ h} = id
pᴹ (1+ t) = pᴹ t ◦ˢᵘᵇ π _

M⃗ = {!!}
