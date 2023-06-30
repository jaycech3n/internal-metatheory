{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.ContextDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SuitableSemicategory I
open import reedy.LinearSieves I

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr

SCT : ℕ → Con
𝔸 : (n : ℕ) → Ty (SCT n)
M : (i h t : ℕ) → shape i h t → Tel (SCT (1+ h))

SCT O = ◆
SCT (1+ n) = SCT n ∷ 𝔸 n

𝔸 O = U
𝔸 (1+ n) = Πₜₑₗ (M (1+ n) n (hom-size (1+ n) n) (full-shape-1+ n)) U

A : (n : ℕ) → Tm[ SCT (1+ n) ] (𝔸 n ʷ)
A n = var (SCT (1+ n))

M i O (1+ t) sh =
  let M' = M i O t (shapeₜ↓ sh) -- (1)
  in M' ‣ wkn el (A O ᵁ) by M'
M i (1+ h) (1+ t) sh =
  let M' = M i (1+ h) t (shapeₜ↓ sh)
  in M' ‣ {!!}
M i (1+ h) O sh = (M i h (hom-size i h) (shapeₕ↓ sh)) [ π _ ]ₜₑₗ
M i O O sh = •

{- Comments

(1) Putting the definition of M' in a where block causes termination errors?...
-}
