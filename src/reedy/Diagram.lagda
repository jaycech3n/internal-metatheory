\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagram {ℓₘᴵ ℓₒ ℓₘ}
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

The beginning cases 𝔻0 and 𝔸0 can just be hardcoded.

\begin{code}

𝔻0 = ◆
𝔸0 = U

\end{code}

Outer induction on h.

\begin{code}

interleaved mutual

  𝔻1+ : ℕ → Con
  𝔸1+ : (n : ℕ) → Ty (𝔻1+ n)

  Mᵒ : (i h t : ℕ) → is-shape i h t → Tel (𝔻1+ h)
  M⃗ : ∀ i h t s {j} (f : hom i j) →
       let r = count-factors i h t s f in
       ∀ (rs : is-shape j h r)
       → Sub (close $ Mᵒ i h t s) (close $ Mᵒ j h r rs)

\end{code}

\begin{code}

  𝔻1+ O = ◆ ∷ U

  A0 : Ty (𝔻1+ O)
  A0 = generic-closed-type-in ◆

  𝔸1+ O = Πₜₑₗ (Mᵒ (1+ O) O (hom-size (1+ O) O) (full-is-shape (1+ O) O)) U

  Mᵒ i O O s = •
  Mᵒ i O (1+ t) s =
    let Mᵒprev = Mᵒ i O t (prev-is-shape s)
    in Mᵒprev ‣ A0 [ πₜₑₗ Mᵒprev ]

  M⃗ i O O s f _ = id
  M⃗ i O (1+ t) s f rs = {!!}

\end{code}

\begin{code}

  𝔻1+ (1+ n) = 𝔻1+ n ∷ 𝔸1+ n

  𝔸1+ (1+ n) =
    Πₜₑₗ (Mᵒ (2+ n) (1+ n) (hom-size (2+ n) (1+ n)) (full-is-shape _ _)) U

  Mᵒ i (1+ h) O s =
    Mᵒ i h (hom-size i h) (full-is-shape _ _) [ π _ ]ₜₑₗ
  Mᵒ i (1+ h) (1+ t) s =
    let A1+h : Ty _
        A1+h = generic- Mᵒ (1+ h) h (hom-size (1+ h) h) (full-is-shape _ _) -indexed-type
    in
    Mᵒ i (1+ h) t (prev-is-shape s) ‣
    A1+h [ {!!} ◦ˢᵘᵇ M⃗ i (1+ h) t {!!} {!!} {!!} ]

  M⃗ i (1+ h) O s f _ = {!!}
  M⃗ i (1+ h) (1+ t) s f rs = {!!}

\end{code}
