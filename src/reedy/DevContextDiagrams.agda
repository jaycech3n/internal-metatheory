{-# OPTIONS --without-K --rewriting --experimental-lossy-unification #-}

open import cwfs.contextual.CwFs
open import cwfs.contextual.Pi
open import cwfs.contextual.Universe
open import reedy.IndexSemicategories

module reedy.DevContextDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  -- {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : ContextualCwF ℓₒ ℓₘ)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves I
open SuitableSemicategory I
open ContextualCwF cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr

M[_,_,_] : (i h t : ℕ) (sh : shape i h t) → Con (#[ i , h , t ] sh)
M : (i : ℕ) → Con (#[ i , i , O ] (full-shape i))
A : (i : ℕ) → Ty (M i)

M[ O , .O , t ] (bounds (inl idp) (inl idp)) = {!!}
M[ O , .O , t ] (bounds (inl idp) (inr u)) = {!!}
M[ 1+ i , h , t ] sh = {!!}

M i = M[ i , i , O ] (full-shape i)

A O = {!!}
A (1+ i) = {!!}
