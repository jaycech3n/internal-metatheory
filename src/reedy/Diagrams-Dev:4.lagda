\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=10 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:4 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I

open import reedy.CosieveShapes I
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

record MatchingData (b : ℕ) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)

matching-data : (b : ℕ) → MatchingData b

𝔻 : (b : ℕ) → Con

record MatchingData b where
  field
    Mᵒ : (i h t : ℕ) (s : is-shape i h t) (bh : h ≤ b) → Tel (𝔻 b)
    M⃗ :
      ∀ i h t s (bh : h ≤ b)
      → {j : ℕ} (f : hom i j)
      → let cf = count-factors i h t s f in
        (cfs : is-shape j h cf)
      → Sub (close $ Mᵒ i h t s bh)
            (close $ Mᵒ j h cf cfs bh)

open MatchingData

𝔻 O = ◆ ∷ U
𝔻 (1+ b) = {!!}

Mᵒ (matching-data O) i h O s bh = •
Mᵒ (matching-data O) i .O (1+ t) s (inl idp) =
  Mᵒ (matching-data O) {!!} {!!} {!!} {!!} {!!}
  -- Agda doesn't like this termination check, I guess because we're referring
  -- to (matching-data O) to define (matching-data O).
M⃗ (matching-data O) = {!!}
matching-data (1+ b) = {!!}

\end{code}
