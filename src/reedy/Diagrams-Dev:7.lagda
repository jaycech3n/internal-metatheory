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

The type of the data of a diagram up to level (b-1), together with
the matching object functor, further refined over shapes.

\begin{code}

record DiagramData (b : ℕ) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)
  where
  field
    𝔻 : Con
    Mᵒ : (sh@(shape i h t s) : Shape) (u : h < b) (w : sh ≤ₛ total-shape b) → Tel 𝔻

  M : (sh@(shape i h t s) : Shape) (u : h < b) (w : sh ≤ₛ total-shape b) → Con
  M sh u w = close (Mᵒ sh u w)

  field
    M⃗ :
      (sh@(shape i h t s) : Shape) (u : h < b) (w : sh ≤ₛ total-shape b)
      → {j : ℕ} (f : hom i j)
      → let rf = count-factors i h t s f in
        (rfs : is-shape j h rf)
      → let rfsh = shape j h rf rfs in
        (rfw : rfsh ≤ₛ total-shape b)
      → Sub (M sh u w) (M rfsh u rfw)

    -- Mᵒₜₒₜ : Tel 𝔻

open DiagramData



diag-data : ∀ b → DiagramData b
Mᵒₜₒₜ : ∀ b → Tel (𝔻 (diag-data b))

diag-data O = record
  { 𝔻 = ◆
  ; Mᵒ = λ{ sh () w }
  ; M⃗ = λ{ sh () w f rfs rfw }
  }
diag-data (1+ b) = record
  { 𝔻 = 𝔻[1+b]
  ; Mᵒ = shape-ind Mᵒ-type (λ{ (shape i h t s) → Mᵒ-rec i h t s })
  ; M⃗ = {!!}
  }
  where
  𝔻[1+b] = 𝔻 (diag-data b) ∷ Πₜₑₗ (Mᵒₜₒₜ b) U

  Mᵒ-type : Shape → Type _
  Mᵒ-type sh@(shape i h t s) =
    (u : h < 1+ b) (w : sh ≤ₛ total-shape (1+ b)) → Tel 𝔻[1+b]

  Mᵒ-rec :
    ∀ i h t s
    → let sh = shape i h t s in
      (rec : ∀ ssh → ssh <ₛ sh → Mᵒ-type ssh)
    → Mᵒ-type sh
  Mᵒ-rec i O O s rec u w = •
  Mᵒ-rec i (1+ h) O s rec u w =
    rec (full-shape i h) (on-ℎ ltS) (S<-< u) {!!}
  Mᵒ-rec i h (1+ t) s rec u w =
    Mᵒ-rec i h t (prev-is-shape s) {!!} u {!!} ‣ {!!}
    -- rec (prev-shape s) (on-𝑡 ltS) u {!!} ‣ {!!}

  -- Mᵒ-rec : ∀ sh → (rec : ∀ ssh → ssh <ₛ sh → Mᵒ-type ssh) → Mᵒ-type sh
  -- Mᵒ-rec (shape i O O s) rec u w = •
  -- Mᵒ-rec (shape i (1+ h) O s) rec u w =
  --   rec (full-shape i h) (on-ℎ ltS) (S<-< u) {!!}
  -- Mᵒ-rec (shape i h (1+ t) s) rec u w =
  --   rec (prev-shape s) (on-𝑡 ltS) u {!!} ‣ {!!}

Mᵒₜₒₜ O = •
Mᵒₜₒₜ (1+ b) = {!!}

\end{code}
