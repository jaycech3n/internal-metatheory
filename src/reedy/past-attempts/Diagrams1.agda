{-# OPTIONS --without-K --rewriting --termination-depth=10 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams1 {ℓₘᴵ ℓₒ ℓₘ}
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
Mᵒ : (i h t : ℕ) → shape i h t → h ≤ i → Tel (𝔻 (1+ h))

-- Convenience definitions ====

M : (i h t : ℕ) → shape i h t → h ≤ i → Con
M i h t s u = close (Mᵒ i h t s u)

Mᵒₜₒₜ : (i : ℕ) → Tel (𝔻 i)
Mᵒₜₒₜ O = •
Mᵒₜₒₜ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i) lteS

𝔸 : (i : ℕ) → Ty (𝔻 i)
𝔸 i = Πₜₑₗ (Mᵒₜₒₜ i) U

A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒₜₒₜ i [ π (𝔸 i) ]ₜₑₗ)
A i = generic[ Mᵒₜₒₜ i ]type

-- End convenience definitions ====

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

M⃗ :
  ∀ i h t s {j} (f : hom i j) (v : h ≤ j)
  → let u = ≤-trans v (inr $ hom-inverse i j f)
        cf = count-factors i h t s f
        sh = count-factors-gives-shape i h t s f
    in Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ i h t s u) (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ j h cf sh v)

Mᵒ O .O t s (inl idp) = •
Mᵒ (1+ h) .(1+ h) t s (inl idp) = Mᵒₜₒₜ (1+ h) [ π (𝔸 (1+ h)) ]ₜₑₗ

Mᵒ .(1+ h) h (1+ t) s (inr ltS) =
  Mᵒ (1+ h) h t shp u ‣ A h [ {!!} ◦ˢᵘᵇ M⃗ (1+ h) h t shp (#[ t ] (1+ h) h v) lteE ]
  where
  shp = prev-shape s
  v = S≤-< s
  u = inr $ hom-inverse (1+ h) h (#[ t ] (1+ h) h v)
Mᵒ .(2+ h) (1+ h) O s (inr ltS) =
  Mᵒ (2+ h) h (hom-size (2+ h) h) shp u [ π (𝔸 (1+ h)) ]ₜₑₗ
  where
  shp = full-shape (2+ h) h
  u = inr (ltSR ltS)
Mᵒ .(1+ O) O O s (inr ltS) = •

Mᵒ (1+ i) h (1+ t) s (inr (ltSR u)) =
  Mᵒ (1+ i) h t shp v ‣ A h [  {!!} ◦ˢᵘᵇ M⃗ (1+ i) h t shp (#[ t ] (1+ i) h w) {!-- (inl idp) here doesn't help the termination checker!} ]
  where
  shp = prev-shape s
  w = S≤-< s
  v = inr $ hom-inverse (1+ i) h (#[ t ] (1+ i) h w)
Mᵒ (1+ i) (1+ h) O s (inr (ltSR u)) =
  Mᵒ (1+ i) h (hom-size (1+ i) h) shp v [ π (𝔸 (1+ h)) ]ₜₑₗ
  where
  shp = full-shape (1+ i) h
  v = lteSR $ inr $ S<-< u
Mᵒ (1+ i) O O s (inr (ltSR u)) = •

{- Old definition; without the h ≤ i condition.

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

-}

M⃗ = {!!}
