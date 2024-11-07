{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-again {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I

import reedy.CosieveShapes as Sh
import reedy.ShapeOrder as Ord
open Sh I
open Ord I

open import reedy.ShapeCountFactors I
open ShapeCountFactors-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ᶜ_ ; ass to assᶜ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

PCl : ℕ → Con
Mᵒ : (i h t : ℕ) (s : is-shape i h t) → Tel (PCl h)
M⃗ : (i h t : ℕ) (s : is-shape i h t) {j : ℕ} (f : hom i j)
     → let r = count-factors i h t s f
           rs = count-factors-is-shape i h t s f
       in Sub (close $ Mᵒ i h t s) (close $ Mᵒ j h r rs)
Mfunc : (i h t : ℕ) (s : is-shape i h t)
        {j : ℕ} (f : hom i j)
        {k : ℕ} (g : hom j k)
        → let r = count-factors i h t s f
              rs = count-factors-is-shape i h t s f
          in idd {!ap ()!} ◦ᶜ M⃗ i h t s (g ◦ f) == M⃗ j h r rs g ◦ᶜ M⃗ i h t s f

PCl = {!!}
Mᵒ = {!!}
M⃗ = {!!}
Mfunc i h t s f g = {!!}
