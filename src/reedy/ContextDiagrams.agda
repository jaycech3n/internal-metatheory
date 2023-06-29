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
M : (i h t : ℕ) → shape i h t → Tel (SCT (1+ h))

SCT O = ◆
SCT (1+ O) = ◆ ∷ U
SCT (2+ n) =
  SCT (1+ n) ∷ Πₜₑₗ (M (1+ n) n (hom-size (1+ n) n) (full-shape-1+ n)) U

M i O (1+ t) sh =
  let M' = M i O t (shapeₜ↓ sh)
    -- Putting this definition in the where block breaks termination checking?..
  in M' ‣ wkn-by M' A₀
  where
    A₀ : Ty (SCT 1)
    A₀ = el (var (SCT 1) ᵁ)
M i (1+ h) (1+ t) sh =
  let M' = M i (1+ h) t (shapeₜ↓ sh)
  in {!M' ‣ ?!}
  where
    A₁₊ₕ : Ty (SCT (1+ h))
    A₁₊ₕ = {!var (SCT (1+ h))!}
M i (1+ h) O sh = (M i h (hom-size i h) (shapeₕ↓ sh)) [ π _ ]ₜₑₗ
M i O O sh = •
