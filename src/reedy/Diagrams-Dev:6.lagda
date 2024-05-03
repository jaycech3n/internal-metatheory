NOTE:
This is a checkpoint save from Diagrams-Dev:5, just before
abstracting 𝔻 over the accessibility predicate as well.

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:5 {ℓₘᴵ ℓₒ ℓₘ}
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

𝔻 : ℕ → Con
Mᵒ : ∀ i h t s (ac : <ₛ-Accc i h t s) → Tel (𝔻 h)

module Convenience where
  M : ∀ i h t s → <ₛ-Accc i h t s → Con
  M i h t s ac = close (Mᵒ i h t s ac)

  -- Total matching context
  Mᵒᵗᵒᵗ[1+_] : ∀ i → <ₛ-Acc (total-shape-1+ i) → Tel (𝔻 i)
  Mᵒᵗᵒᵗ[1+ i ] = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-is-shape-1+ i)

  𝔸[1+_] : ∀ i → Ty (𝔻 i)
  𝔸[1+ i ] = Πₜₑₗ (Mᵒᵗᵒᵗ[1+ i ] {!!}) U

open Convenience

𝔻 O = ◆ ∷ U
𝔻 (1+ h) = 𝔻 h ∷ Πₜₑₗ (Mᵒ (1+ h) h tot ts <ₛ-is-wf) U
  where
  tot = hom-size (1+ h) h
  ts = total-is-shape-1+ h

M⃗ : ∀ i h t s (ac : <ₛ-Accc i h t s)
     → {j : ℕ} (f : hom i j)
     → let r = count-factors i h t s f in
       (rs : is-shape j h r)
     → (·-ac : <ₛ-Accc j h r rs)
     → Sub (close $ Mᵒ i h t s ac) (close $ Mᵒ j h r rs ·-ac)

Mᵒ i O O s ac = •
Mᵒ i (1+ h) O s ac = wkₜₑₗ $ Mᵒ i h (hom-size i h) (full-is-shape i h) <ₛ-is-wf
Mᵒ i O (1+ t) s (acc _ rec) =
  let
    prev-acc = rec _ (on-𝑡 ltS)
    prev-Mᵒ = Mᵒ i O t prev-s prev-acc
  in
    prev-Mᵒ ‣ A₀ [ πₜₑₗ prev-Mᵒ ]
  where
    prev-s = prev-is-shape s
    A₀ : Ty (𝔻 O)
    A₀ = generic[ ◆ ]type

Mᵒ i (1+ h) (1+ t) s (acc _ rec) =
  let
    prev-acc = rec _ (on-𝑡 ltS)
    ·-acc = rec _ (on-𝑖 (hom-inverse _ _ [t]))
  in
    Mᵒ i (1+ h) t prev prev-acc
      ‣ Aₕ₊₁ [ idd {!!} ◦ˢᵘᵇ M⃗ i (1+ h) t prev prev-acc [t] rs ·-acc ]
  where
    prev = prev-is-shape s
    u = <-from-is-shape s
    [t] = #[ t ] i (1+ h) u

    Aₕ₊₁ : Ty (𝔻 (1+ h) ++ₜₑₗ wkₜₑₗ (Mᵒᵗᵒᵗ[1+ h ] _))
    Aₕ₊₁ = generic[ _ ; Mᵒᵗᵒᵗ[1+ h ] <ₛ-is-wf ]type

    rs = count-factors-is-shape i (1+ h) t prev [t]


M⃗ i O t s ac f rs ·-acc = {!!}
M⃗ i (1+ h) t s ac f rs ·-acc = {!!}

\end{code}
