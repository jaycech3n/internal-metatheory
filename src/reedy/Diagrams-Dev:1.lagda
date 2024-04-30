\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:1 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I

open import reedy.CosieveShapes I
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

record DiagramDataType (bsh : Shape) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) where
  field
    𝔻 : Con
    Mᵒ : (sh : Shape) → sh ≤ₛ bsh → Tel 𝔻
    M⃗ :
      (sh@(shape i h t s) : Shape)
      (w : sh ≤ₛ bsh)
      {j : ℕ} (f : hom i j)
      → let cf = count-factors i h t s f in
        (cfs : is-shape j h cf)
      → Sub (close $ Mᵒ sh w)
            (close $ Mᵒ (shape j h cf cfs) (≤ₛ-trans (restr-≤ₛ-decr sh f cfs) w))

DiagramData : (sh : Shape) → DiagramDataType sh
DiagramData sh = ?

\end{code}
