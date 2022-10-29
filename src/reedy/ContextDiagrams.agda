{-# OPTIONS --without-K #-}

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.ContextDiagrams {ℓₘᴵ ℓₒ ℓₘ ℓᵀʸ ℓᵀᵐ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure ℓᵀʸ ℓᵀᵐ C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves I
open SuitableSemicategory I
open CwFStructure cwfstr
open PiStructure pistr
open UniverseStructure univstr

SCT : ℕ → Con
Sk : (n i h t : ℕ) → i ≤ n → is-shape i h t → Con

SCT O = ◆
SCT (1+ n) = SCT n ∷ {!!}

Sk n (1+ i) O O u iS = SCT n
Sk n (1+ i) O (1+ t) u iS = Sk n (1+ i) O t u (shape-from-next-t iS) ∷ {!!}
Sk n (1+ i) (1+ h) O u iS = Sk n (1+ i) h (hom-size (1+ i) h) u (shape-from-next-h iS)
Sk n (1+ i) (1+ h) (1+ t) u iS = {!!}
