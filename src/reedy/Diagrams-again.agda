{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-again {ℓₘᴵ ℓₒ ℓₘ}
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

open CwFStructure cwfstr renaming (_◦_ to _◦ᶜ_ ; ass to assᶜ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

record Data (b : ℕ) : Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) where
  field
    𝔻 : (h : ℕ) → h ≤ b → Con
    M : (sh : Shape) → (u : ℎ sh ≤ b) → Tel (𝔻 (ℎ sh) u)
    M⃗ :
      (sh : Shape) (u : ℎ sh ≤ b)
      {j : ℕ} (f : hom (𝑖 sh) j)
      → Sub (close $ M sh u) (close $ M (rstrₛ sh f) u)
    -- ...

F : (b : ℕ) → Data b

F O = record
  { 𝔻 = λ _ _ → ◆
  ; M = shape-ind _ λ
    { (shape i h O s) M u → •
    ; (shape i h (1+ t) s) M u → M (shape i h t (prev-is-shape s)) (on-𝑡 ltS) u ‣ U
    }
  ; M⃗ = shape-ind _ λ
    { (shape i h O s) M⃗ u f → id
    ; (shape i h (1+ t) s) M⃗ u f → {!
      -- Now we need to arrange for the type of this hole, which is in terms of
      -- the induction hypothesis, to compute to the right thing depending on
      -- whether or not f divides [t] : hom i h.
      -- Also need to do so in a way that termination-checks, but for now I'm
      -- willing to cut this corner.
      !}
    }
  }

F (1+ b) = {!!}
