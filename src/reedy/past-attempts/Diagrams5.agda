{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams5 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I
open import reedy.Cosieves I
open Cosieves-IsStrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr


record DiagramData (s₀ : Shape) : Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) where
  field
    𝔻  : Con
    Mᵒ : (s : Shape) → s ≤ₛ s₀ → Tel 𝔻

  M : (s : Shape) → s ≤ₛ s₀ → Con
  M s u = close (Mᵒ s u)

  field
    M⃗ : (s : Shape) (u : s ≤ₛ s₀)
         → {j : ℕ} (f : hom (𝑖 s) j) (v : s · f ≤ₛ s₀)
         → Sub (M s u) (M (s · f) v)
    α  : (s : Shape) (u : s ≤ₛ s₀)
         → {j : ℕ} (f : hom (𝑖 s) j)
         → {k : ℕ} (g : hom j k)
         → (M⃗ {!s · f!} {!lemma!} g {!!}) ◦ˢᵘᵇ (M⃗ s u f {!!}) == {!M⃗ s u (g ◦ f) ?!}


Diagram : (s : Shape) → DiagramData s
Diagram s = shape-ind DiagramData {!!} s
