\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:8 {ℓₘᴵ ℓₒ ℓₘ}
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

record DiagramData (b : ℕ) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) where
  field 𝔻 : Con

  MatchingFunctor : (sh₀ : Shape) (bd₀ : ℎ sh₀ < b) → Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)
  MatchingFunctor sh₀ bd₀ =
    Σ[ Mᵒ ﹕
      ((sh : Shape) (bd : ℎ sh < b) (w : sh ≤ₛ sh₀) → Tel 𝔻) ]
    Σ[ M⃗ ﹕
      ((sh@(shape i h t s) : Shape) (bd : ℎ sh < b) (w : sh ≤ₛ sh₀)
      {j : ℕ} (f : hom i j)
      → let rf = count-factors i h t s f
            rfs = count-factors-is-shape i h t s f
            rfw = ≤ₛ-trans (rstr-≤ₛ-decr sh f rfs) w
        in
        Sub (close $ Mᵒ sh bd w) (close $ Mᵒ (shape j h rf rfs) bd rfw)) ]
    ( (sh@(shape i h t s) : Shape) (bd : ℎ sh < b) (w : sh ≤ₛ sh₀)
      {j : ℕ} (f : hom i j)
      {k : ℕ} (g : hom j k)
      → let rf = count-factors i h t s f
            rfs = count-factors-is-shape i h t s f
            rfw = ≤ₛ-trans (rstr-≤ₛ-decr sh f rfs) w
        in
        M⃗ (shape j h rf rfs) bd rfw g ◦ˢᵘᵇ M⃗ sh bd w f
        == idd {!ap2 (λ rf w' → Mᵒ (shape k (ℎ sh) rf rfs) bd w' ) ?!} ◦ˢᵘᵇ M⃗ sh bd w (g ◦ f) )

  field M : (sh₀ : Shape) (bd₀ : ℎ sh₀ < b) → MatchingFunctor sh₀ bd₀

open DiagramData

diag-data : (b : ℕ) → DiagramData b

diag-data O = record { 𝔻 = ◆ ; M = λ{ _ () } }

diag-data (1+ O) = record
  { 𝔻 = ◆ ∷ U
  ; M = λ
    { (Sh.shape i₀ O O s₀) bd₀ → {!!}
    ; (Sh.shape i₀ (1+ h₀) O s₀) bd₀ → {!!}
    ; (Sh.shape i₀ h₀ (1+ t₁) s₀) bd₀ → {!!}
    }
  }
  where
  --

diag-data (2+ b) = record { 𝔻 = {!!} ; M = {!!} }

\end{code}
