\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=10 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:2 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I

import reedy.CosieveShapes as Sh
open Sh I

open import reedy.ShapeOrder I
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

𝔻 : (bsh sh : Shape) → sh ≤ₛ bsh → Con
Mᵒ : (bsh sh : Shape) (w : sh ≤ₛ bsh) → Tel (𝔻 bsh sh w)
M⃗ : (bsh sh@(shape i h t s) : Shape) (w : sh ≤ₛ bsh) {j : ℕ} (f : hom i j)
     → let cf = count-factors i h t s f in
       (cfs : is-shape j h cf)
     → Sub (close $ Mᵒ bsh sh w)
           (close $ Mᵒ bsh (shape j h cf cfs) (≤ₛ-trans (restr-≤ₛ-decr sh f cfs) w))

𝔻 (shape O bh bt bs) sh w = ◆

𝔻 bsh@(shape (1+ bi) bh (1+ bt) bs) .(shape (1+ bi) bh (1+ bt) bs) (inl idp) =
  𝔻 bsh (shape (1+ bi) bh bt (prev-is-shape bs)) (inr (on-𝑡 ltS)) ∷ {!!}
  -- Why the failed termination check?
𝔻 bsh@(shape (1+ bi) O O bs) sh (inl p) =
  𝔻 bsh (shape bi bi O (O≤ _)) (inr (on-𝑖 ltS))
𝔻 bsh@(shape (1+ bi) (1+ bh) O bs) sh (inl p) =
  𝔻 bsh (full-shape (1+ bi) bh) (inr (on-ℎ ltS))

𝔻 (shape (1+ bi) O O bs) sh (inr x) = {!!}
𝔻 (shape (1+ bi) (1+ bh) O bs) sh (inr x) = {!!}
𝔻 (shape (1+ bi) bh (1+ bt) bs) sh (inr x) = {!!}

Mᵒ = {!!}

M⃗ = {!!}

\end{code}
