{-# OPTIONS --without-K #-}

open import cwfs.Contextual
open import cwfs.Pi
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.ContextDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (ccwfstr : ContextualCwFStructure C)
  (pistr : PiStructure (ContextualCwFStructure.cwfstr ccwfstr))
  (univstr : UniverseStructure (ContextualCwFStructure.cwfstr ccwfstr))
  where

open import reedy.LinearSieves I
open SuitableSemicategory I
open ContextualCwFStructure ccwfstr
open PiStructure pistr
open UniverseStructure univstr

SCT : ℕ → Con
Sk : (n i h t : ℕ) → i ≤ n → is-shape i h t → Con

SCT O = ◆
SCT (1+ n) = SCT n ∷ {!!}

Sk n i O O u iS = SCT n
Sk n i O (1+ t) u iS = Sk n i O t u (shapeₜ↓ iS) ∷ {!!}
Sk n i (1+ h) O u iS = Sk n i h (hom-size i h) u (shapeₕ↓ iS)
Sk n i (1+ h) (1+ t) u iS = {!!}
