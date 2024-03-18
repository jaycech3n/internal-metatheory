{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.ContextDiagramsDev {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SuitableSemicategory I
open import reedy.LinearSievesDev I

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr

𝔻 : ℕ → Con
Mᵒ[_] : (i : ℕ) → Tel (𝔻 i)
-- Μᵒ : (i h t : ℕ) → shape i h t → Tel (𝔻 {!!})

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ Πₜₑₗ Mᵒ[ i ] U

𝔸 : (i : ℕ) → Ty (𝔻 i)
𝔸 i = Πₜₑₗ Mᵒ[ i ] U

A : (i : ℕ) → Ty (𝔻 (1+ i) ++ₜₑₗ wkₜₑₗ Mᵒ[ i ])
A i = el (f (υ _))
  where
  e : 𝔸 i [ π (𝔸 i) ] == Πₜₑₗ (wkₜₑₗ Mᵒ[ i ]) U
  e = Πₜₑₗ[] Mᵒ[ i ] _ (π _) ∙ ap (Πₜₑₗ (wkₜₑₗ Mᵒ[ i ])) U[]

  f : Tm (𝔸 i [ π (𝔸 i) ]) → Tm[ 𝔻 (1+ i) ++ₜₑₗ wkₜₑₗ Mᵒ[ i ] ] U
  f = appₜₑₗ (wkₜₑₗ Mᵒ[ i ]) ∘ transp Tm e

Mᵒ[ i ] = {!!}

-- Μᵒ i h t sh = {!!}
