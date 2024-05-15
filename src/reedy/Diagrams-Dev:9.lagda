\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:9 {ℓₘᴵ ℓₒ ℓₘ}
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

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

\end{code}

\begin{code}

record Match (b : ℕ) (bsh : [ b ]BoundedShape) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)
𝔻 : (b : ℕ) → Con
MF : (b : ℕ) (bsh : [ b ]BoundedShape) → Match b bsh

record Match b bsh where
  eta-equality
  field Mᵒ : (bsh' : [ b ]BoundedShape) → bsh' ≤ₛᵇ bsh → Tel (𝔻 b)

  M : (bsh' : [ b ]BoundedShape) → bsh' ≤ₛᵇ bsh → Con
  M bsh' w = close $ Mᵒ bsh' w

  field
    M⃗ :
      (bsh'@(shape i' h' t' s' , u') : [ b ]BoundedShape)
      (w : bsh' ≤ₛᵇ bsh)
      {j : ℕ} (f : hom i' j)
      → let r = count-factors i' h' t' s' f in
        (rs : is-shape j h' r)
      → let rsh = shape j h' r rs , u' in
        (rw : rsh ≤ₛᵇ bsh)
      → Sub (M bsh' w) (M rsh rw)

Mᵒ : (b : ℕ) (bsh bsh' : [ b ]BoundedShape) → bsh' ≤ₛᵇ bsh → Tel (𝔻 b)
Mᵒ b = Match.Mᵒ ∘ MF b

𝔻 O = ◆
𝔻 (1+ O) = ◆ ∷ U
𝔻 (2+ b) = 𝔻 (1+ b) ∷ Πₜₑₗ (Mᵒ (1+ b) tot tot (inl idp)) U
  where tot = total-shape-1+ b , ltS

MF (1+ O) bsh = {!!}
MF (2+ b) bsh = {!!}

\end{code}
