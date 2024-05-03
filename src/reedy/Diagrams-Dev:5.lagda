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

  Mᵒtot[1+_] : (h : ℕ) → <ₛ-Acc (total-shape-1+ h) → Tel (𝔻 h)
  Mᵒtot[1+ h ] = Mᵒ (1+ h) h (hom-size (1+ h) h) (total-is-shape-1+ h)

  Mᵒfull : (i h : ℕ) → <ₛ-Acc (full-shape i h) → Tel (𝔻 h)
  Mᵒfull i h = Mᵒ i h full shp
    where
    full = hom-size i h
    shp = full-is-shape i h

  -- 𝔸 : (i : ℕ) → Ty (𝔻 i)
  -- 𝔸 i = Πₜₑₗ (Mᵒᵗᵒᵗ i) U

  -- A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ)
  -- A i = generic[ Mᵒᵗᵒᵗ i ]type

open Convenience

𝔻 O = ◆
𝔻 (1+ h) = 𝔻 h ∷ {!Πₜₑₗ (Mᵒ (1+ h) h tot ts <ₛ-is-wf) U!}
  where
  tot = hom-size (1+ h) h
  ts = total-is-shape-1+ h

M⃗ : ∀ i h t s (ac : <ₛ-Accc i h t s)
     → {j : ℕ} (f : hom i j)
     → let r = count-factors i h t s f in
       (rs : is-shape j h r)
     → (·-ac : <ₛ-Accc j h r rs)
     → Sub (M i h t s ac) (M j h r rs ·-ac)

Mᵒ i O O s ac = •
Mᵒ i (1+ h) O s ac = {!Mᵒ i h (hom-size i h) (full-is-shape i h) ? [ π ]!}
Mᵒ i O (1+ t) s (acc _ rec) = {!!}
Mᵒ i (1+ h) (1+ t) s (acc _ rec) =
  let prev-acc = rec _ (on-𝑡 ltS)
      ·-acc = rec _ (on-𝑖 (hom-inverse _ _ [t]))
  in
  Mᵒ i (1+ h) t prev prev-acc
    ‣ Aₕ [ idd {!!} ◦ˢᵘᵇ M⃗ i (1+ h) t prev prev-acc [t] rs ·-acc ]
  where
    prev = prev-is-shape s

    u = <-from-is-shape s
    [t] = #[ t ] i (1+ h) u

    tot = hom-size (1+ h) h
    ts = total-is-shape-1+ h

    tot-acc : <ₛ-Acc (total-shape-1+ h)
    tot-acc = rec (shape (1+ h) h tot ts) (on-𝑖 (hom-inverse _ _ [t]))

    Aₕ = generic[ _ ; Mᵒ (1+ h) h tot ts tot-acc ]type

    rs = count-factors-is-shape i (1+ h) t prev [t]


M⃗ i h t s ac f rs ·-acc = {!!}

\end{code}
