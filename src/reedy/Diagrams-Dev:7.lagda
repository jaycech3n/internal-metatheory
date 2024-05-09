\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:7 {ℓₘᴵ ℓₒ ℓₘ}
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

record DiagramData (bsh : BoundedShape) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) where
  lsh : Shape
  lsh = 𝑠ℎ bsh

  b = 𝑏 bsh

  field
    𝔻 : Con
    Mᵒ : (sh : Shape) (u : ℎ sh < b) (w : sh ≤ₛ lsh) → Tel 𝔻

  M : (sh : Shape) (u : ℎ sh < b) (w : sh ≤ₛ lsh) → Con
  M sh u w = close $ Mᵒ sh u w

  field
    M⃗ :
      (sh@(shape i h t s) : Shape)
      (u : ℎ sh < b)
      (w : sh ≤ₛ lsh)
      {j : ℕ} (f : hom i j)
      → let rf = count-factors i h t s f
            rfs = count-factors-is-shape i h t s f
            rfw = ≤ₛ-trans (rstr-≤ₛ-decr sh f rfs) w
        in
        Sub (M sh u w)
            (M (shape j h rf rfs) u rfw)

open DiagramData

[_] : ∀ b i h t s lu → DiagramData (bdd (shape i h t s) b lu)

𝔻 ([ 1+ O ] O O O s lu) = ◆ ∷ U
Mᵒ ([ 1+ O ] O O O s lu) sh u w = •
M⃗ ([ 1+ O ] O O O s lu) sh u w f = id

[ 1+ O ] O O (1+ t) s lu =
  let rec = [ 1+ O ] O O t (prev-is-shape s) lu in
  record
  { 𝔻 = 𝔻 rec
  ;
    Mᵒ =
    λ{ sh u (inl p) → {!!}
     ; sh u (inr w) → Mᵒ rec sh u (<ₛS𝑡-≤ₛ𝑡 _ w) }
  ;
    M⃗ = {!!}
  }

[ 1+ O ] O (1+ h) t s (ltSR ())

[ 1+ O ] (1+ i) O O s lu =
  let rec = [ 1+ O ] i O (hom-size i O) (full-is-shape i O) lu in
  record
  { 𝔻 = 𝔻 rec
  ;
    Mᵒ =
    λ{ sh u (inl p) → Mᵒ rec (full-shape i O) ltS (inl idp)
     ; sh u (inr w) → Mᵒ rec sh u (<ₛ-improper₀-≤ₛ-full _ i u w) }
  ;
    M⃗ = λ sh u w f → {!!}
  }

-- There seems to be a difference in normalization/unification for definitions
-- by copattern vs definitions by record: the following copattern version of the
-- above clause doesn't typecheck.
-- 𝔻 ([ 1+ O ] (1+ i) O O s lu) = 𝔻 rec
--   where rec = [ 1+ O ] i O (hom-size i O) (full-is-shape i O) lu
-- Mᵒ ([ 1+ O ] (1+ i) O O s lu) sh u (inl p) =
--   Mᵒ rec (full-shape i O) ltS (inl idp)
--   where rec = [ 1+ O ] i O (hom-size i O) (full-is-shape i O) lu
-- Mᵒ ([ 1+ O ] (1+ i) O O s lu) sh u (inr w) = Mᵒ rec sh u (<ₛ-improper₀-≤ₛ-full _ i u w)
--   where rec = [ 1+ O ] i O (hom-size i O) (full-is-shape i O) lu
-- M⃗ ([ 1+ O ] (1+ i) O O s lu) = {!!}

[ 1+ O ] (1+ i) O (1+ t) s lu = {!!}

[ 1+ O ] (1+ i) (1+ h) t s (ltSR ())


[ 2+ b ] i h t s lu = {!!}

{-
diagram-data[_] : ∀ b i h t s u → DiagramData (bdd (shape i h t s) b u)

𝔻 (diagram-data[ 1+ O ] O O O s u) = ◆ ∷ U
Mᵒ (diagram-data[ 1+ O ] O O O s u) sh w = •
M⃗ (diagram-data[ 1+ O ] O O O s u) sh w f = id

𝔻 (diagram-data[ 1+ O ] O O (1+ t) s u) = -- ◆ ∷ U
  𝔻 (diagram-data[ 1+ O ] O O t (prev-is-shape s) u)
Mᵒ (diagram-data[ 1+ O ] O O (1+ t) s u) = {!!}
M⃗ (diagram-data[ 1+ O ] O O (1+ t) s u) = {!!}

diagram-data[ 1+ O ] (1+ i) O O s u = record
  { 𝔻 = 𝔻 rec
  ; Mᵒ =
    λ{ sh (inl p) → Mᵒ rec (full-shape i O) (inl idp)
     ; sh (inr w) → {!Mᵒ rec sh!} }
  ; M⃗ = {!!} }
  where rec = diagram-data[ 1+ O ] i O (hom-size i O) (full-is-shape i O) u

-- 𝔻 (diagram-data[ 1+ O ] (1+ i) O O s u) = -- ◆ ∷ U
--   𝔻 (diagram-data[ 1+ O ] i O (hom-size i O) (full-is-shape i O) u)
-- Mᵒ (diagram-data[ 1+ O ] (1+ i) O O s u) sh (inl p) =
--   Mᵒ (diagram-data[ 1+ O ] i O (hom-size i O) (full-is-shape i O) u) (full-shape i O) {!!}
-- Mᵒ (diagram-data[ 1+ O ] (1+ i) O O s u) sh (inr (on-𝑖 w)) =
--   Mᵒ (diagram-data[ 1+ O ] i O (hom-size i O) {!!} {!!}) sh {!!}
-- M⃗ (diagram-data[ 1+ O ] (1+ i) O O s u) = {!!}

diagram-data[ 1+ O ] (1+ i) O (1+ t) s u = {!!}


diagram-data[ 1+ O ] O (1+ h) t s (ltSR ())
diagram-data[ 1+ O ] (1+ i) (1+ h) t s (ltSR ())

diagram-data[ 2+ b ] i h t s u = {!!}
-}


\end{code}
