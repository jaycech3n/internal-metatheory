{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams3 {ℓₘᴵ ℓₒ ℓₘ}
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
Mᵒ[_] : (i₀ i h t : ℕ) → i ≤ i₀ → shape i h t → Tel (𝔻 (1+ h))

-- Convenience definitions ====

Mᵒ : (i h t : ℕ) → shape i h t → Tel (𝔻 (1+ h))
Mᵒ i h t s = Mᵒ[ i ] i h t lteE s

M : (i h t : ℕ) → shape i h t → Con
M i h t s = close (Mᵒ i h t s)

Mᵒₜₒₜ : (i : ℕ) → Tel (𝔻 i)
Mᵒₜₒₜ O = •
Mᵒₜₒₜ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

𝔸 : (i : ℕ) → Ty (𝔻 i)
𝔸 i = Πₜₑₗ (Mᵒₜₒₜ i) U

A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒₜₒₜ i [ π (𝔸 i) ]ₜₑₗ)
A i = generic[ Mᵒₜₒₜ i ]type

-- End convenience definitions ====

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

-- Change this
M⃗ :
  ∀ i₀ i h t (u : i ≤ i₀) (s : shape i h t) {j} (f : hom i j)
  → let cf = count-factors i h t s f
        sh = count-factors-gives-shape i h t s f
    in Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ[ i₀ ] i h t s)
           (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ[ i₀ ] j h cf sh)

Mᵒ[ O ] i h (1+ t) u s =
  Mᵒ[ O ] i h t u shp ‣ A h [ {!!} ◦ˢᵘᵇ {!M⃗ !} ]
  where
  shp = prev-shape s
Mᵒ[ O ] i (1+ h) O u s = Mᵒ[ O ] i h full u shp [ π (𝔸 (1+ h)) ]ₜₑₗ
  where
  full = hom-size i h
  shp = full-shape i h
Mᵒ[ O ] i O O u s = •

Mᵒ[ 1+ i₀ ] i h t u s = {!!}

M⃗ = {!!}


{-
Mᵒ i h (1+ t) s =
  Mᵒ i h t shp ‣ A h [ {!!} ◦ˢᵘᵇ M⃗ i h t shp (#[ t ] i h u) ]
  where
  shp = prev-shape s
  u : t < hom-size i h
  u = S≤-< s
Mᵒ i (1+ h) O s = Mᵒ i h full shp [ π (𝔸 (1+ h)) ]ₜₑₗ
  where
  full = hom-size i h
  shp = full-shape i h
Mᵒ i O O s = •

M⃗ i h (1+ t) s f = {!!}
M⃗ i (1+ h) O s f = {!M⃗ i h full shp f!}
  where
  full = hom-size i h
  shp = full-shape i h
M⃗ i O O s f = id
-}
