{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

{--- IMPORTANT! This version switches off termination checking temporarily. ---}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams4 {ℓₘᴵ ℓₒ ℓₘ}
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


record DiagramData (s : Shape) : Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) where
  field
    𝔻  : Con
    Mᵒ : (s' : Shape) → (s' ≤ₛ s) → Tel 𝔻
    M⃗ : (s' : Shape) (u : s' ≤ₛ s)
       → {j : ℕ} (f : hom (𝑖 s') j)
       → Sub (close $ Mᵒ s (inl idp)) -- why is this not (Mᵒ s' u) again?
             (close $ Mᵒ {!s' · f!}  {!inr $ lemma : s' · f <ₛ s!})
    α  : {s' : Shape} (p : (s' ≤ₛ s))
       → {j : ℕ} (f : hom (𝑖 s') j)
       → {k : ℕ} (g : hom j k)
       → (M⃗ {!s' ◦ f!} {!lemma!} g) ◦ˢᵘᵇ (M⃗ s' p f) == M⃗ s' p (g ◦ f)


Diagram : (s : Shape) → DiagramData s
Diagram s = shape-ind DiagramData {!!} s
