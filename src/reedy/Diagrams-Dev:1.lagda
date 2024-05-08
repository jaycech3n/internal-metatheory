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

-- This definition is wrong.
record DiagramDataType (b : ℕ) (sh : Shape) (u : ℎ sh ≤ b) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) where
  field
    𝔻 : Con -- Contains filler types up to what level?
            -- • bh, where bsh = (bi, bh, bt)? Can't be, because could have e.g.
            -- bsh = (10,0,0) and sh = (9,8,full), and we'd need Mᵒ (9,8,full)
            -- in context 𝔻 with the 8-filler.
            -- • bi -1? But we'd have to define Mᵒ (i,h,t) in general, where we
            -- could have bi -1 < h for shapes. Then we'd need to do something like
            -- discriminate on whether bi -1 < h or bi -1 ≥ h.
    Mᵒ : (sh : Shape) → sh ≤ₛ bsh → Tel 𝔻 -- wrong.
    M⃗ :
      (sh@(shape i h t s) : Shape)
      (w : sh ≤ₛ bsh)
      {j : ℕ} (f : hom i j)
      → let cf = count-factors i h t s f in
        (cfs : is-shape j h cf)
      → Sub (close $ Mᵒ sh w)
            (close $ Mᵒ (shape j h cf cfs) (≤ₛ-trans (restr-≤ₛ-decr sh f cfs) w))

open DiagramDataType

DiagramDataRec : (bsh : Shape) → Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)
DiagramDataRec bsh = (sh : Shape) → sh <ₛ bsh → DiagramDataType sh

rstr :
  ∀ {bsh} → DiagramDataRec bsh
  → (sh : Shape) → sh <ₛ bsh → DiagramDataRec sh
rstr ind sh w = λ sh' w' → ind sh' (<ₛ-trans w' w)

diagram-data-aux :
  ∀ bi bh bt bs
  → DiagramDataRec (shape bi bh bt bs)
  → DiagramDataType (shape bi bh bt bs)
diagram-data-aux bi bh (1+ bt) bs ind = {!!}
diagram-data-aux bi (1+ bh) O bs ind = record
  { 𝔻 = prev-𝔻 ∷ Πₜₑₗ {!Mᵒ!} U
  ; Mᵒ = {!!}
  ; M⃗ = λ sh w f cfs → {!!} }
  where
  diagram[i,h,full] =
    diagram-data-aux bi bh (hom-size bi bh) (full-shape bi bh) (rstr ind _ (on-ℎ ltS))
  prev-𝔻 = 𝔻 diagram[i,h,full]
  -- Mᵒ[1+h] = \Mᵒ

diagram-data-aux bi O O bs ind = record
  { 𝔻 = ◆ ∷ U
  ; Mᵒ = λ{ .(shape bi O O bs) (inl idp) → • ; sh (inr (on-𝑖 w)) → {!!} }
  ; M⃗ = λ sh w f cfs → {!!} }


diagram-data : (bsh : Shape) → DiagramDataType bsh
diagram-data =
  shape-ind
    DiagramDataType
    λ{(shape bi bh bt bs) → diagram-data-aux bi bh bt bs}

\end{code}
