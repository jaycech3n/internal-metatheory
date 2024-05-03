\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=10 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:3 {ℓₘᴵ ℓₒ ℓₘ}
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

open import reedy.ShapeOrder:1 I
open import reedy.ShapeCountFactors:1 I
open ShapeCountFactors-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

\end{code}

\begin{code}

𝔻[_,_,_,_] :
  (bi bh bt : ℕ) (bs : is-shape bi bh bt)
  (i h t : ℕ) (s : is-shape i h t)
  → [ i , h , t , s ]≤[ bi , bh , bt , bs ]
  → Con

\end{code}

The idea of the above is that
  𝔻[ bi , bh , bt , bs ] _ _ _ _ _ _
contains Aₖ : 𝔸ₖ sufficient for all (i, h, t) ≤ (bi, bh, bt).
In particular, i ≤ bi and so we need only worry about the case h ≤ bi.

\begin{code}

Mᵒ[_,_,_,_] :
  (bi bh bt : ℕ) (bs : is-shape bi bh bt)
  (i h t : ℕ) (s : is-shape i h t)
  (w : [ i , h , t , s ]≤[ bi , bh , bt , bs ])
  → Tel (𝔻[ bi , bh , bt , bs ] i h t s w)
M⃗[_,_,_,_] :
  (bi bh bt : ℕ) (bs : is-shape bi bh bt)
  (i h t : ℕ) (s : is-shape i h t)
  (w : [ i , h , t , s ]≤[ bi , bh , bt , bs ])
  {j : ℕ} (f : hom i j)
  → let cf = count-factors i h t s f in
    (cfs : is-shape j h cf)
  → let rstr-bdd = ≤ₛ-trans (rstr-≤ₛ-decr i h t s f  cfs) w in
    Sub (close $ Mᵒ[ bi , bh , bt , bs ] i h t s w)
        (close $ Mᵒ[ bi , bh , bt , bs ] j h cf cfs rstr-bdd)

𝔻[ O , bh , bt , bs ] i h t s w = ◆

𝔻[ 1+ bi , bh , 1+ bt , bs ] _ _ _ _ _ =
  𝔻[ 1+ bi , bh , bt , ps ] (1+ bi) bh bt ps idp
  where ps = prev-is-shape bs
𝔻[ 1+ bi , 1+ bh , O , bs ] _ _ _ _ _ =
  𝔻[ 1+ bi , bh , full , fs ] (1+ bi) bh full fs idp
  ∷ Πₜₑₗ {!Mᵒ[ 1+ bi , bh , full , fs ] !} U
  where
  full = hom-size (1+ bi) bh
  fs = full-is-shape (1+ bi) bh
𝔻[ 1+ bi , O , O , bs ] _ _ _ _ = {!𝔻!}

-- 𝔻[ 1+ bi , bh , 1+ bt , bs ] .(1+ bi) .bh .(1+ bt) .bs idp =
--   𝔻[ 1+ bi , bh , 1+ bt , bs ] (1+ bi) bh bt (prev-is-shape bs) (inr (on-𝑡 ltS))
-- 𝔻[ 1+ bi , O , O , bs ] .(1+ bi) .O .O .bs idp =
--   𝔻[ 1+ bi , O , O , bs ] bi bi O (O≤ _) (inr (on-𝑖 ltS))
-- 𝔻[ 1+ bi , 1+ bh , O , bs ] .(1+ bi) .(1+ bh) .O .bs idp =
--   𝔻[ 1+ bi , 1+ bh , O , bs ]
--     (1+ bi) bh (hom-size (1+ bi) bh) (full-is-shape _ _) (inr (on-ℎ ltS))
--     ∷ Πₜₑₗ {!Mᵒ[  ]!} U

-- 𝔻[ 1+ bi , bh , 1+ bt , bs ] i h t s (inr w) = {!!}
-- 𝔻[ 1+ bi , O , O , bs ] i h t s (inr w) = {!w!}
-- 𝔻[ 1+ bi , 1+ bh , O , bs ] i h t s (inr w) =
--   𝔻[ 1+ bi , bh , hom-size (1+ bi) bh , full-is-shape _ _ ] {!!} {!!} {!!} {!!} {!!}

Mᵒ[ O , bh , bt , bs ] i h t s w = {!!}
Mᵒ[ 1+ bi , bh , bt , bs ] i h t s w = {!!}

M⃗[ bi , bh , bt , bs ] i h t s w f cfs = {!!}

\end{code}
