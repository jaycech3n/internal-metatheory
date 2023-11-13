{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams2 {ℓₘᴵ ℓₒ ℓₘ}
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

open import reedy.ShapeElimination I using (shape-elim)

-- Refer to Diagrams.agda for the informal mutually inductive def.

Diag : (i h t : ℕ) (s : shape i h t)
  → Σ[ Comps ː Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) ] -- types of the diagram components
    Comps -- actual diagram components
𝔻 : ∀ i h t s → fst (Diag i h t s) → Con

Diag O h t s =
  ( Σ[ 𝔻' ː Con ]
    Σ[ Mᵒ' ː Tel (𝔻' ∷ U) ]
    ( ∀ {j} (f : hom O j) → Sub (𝔻' ∷ U ++ₜₑₗ Mᵒ') (𝔻' ∷ U) ) )
  ,
  ◆ , • , λ _ → id
Diag (1+ i) h (1+ t) s = {!!}
Diag (1+ i) (1+ h) O s = {!!}
Diag (1+ i) O O s =
  ( Σ[ 𝔻' ː Con ]
    Σ[ Mᵒ' ː Tel (𝔻' ∷ U) ]
    ( {!∀ {j} (f : hom i j)
      → Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ i h t s) (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ j h cf sh)!} ) )
  ,
  {!!}

𝔻 i h t s = {!!}


{- OLD: ====

DiagramComps : (i h t : ℕ) (s : shape i h t) → Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ)
diagram-comps : (i h t : ℕ) (s : shape i h t) → DiagramComps i h t s
𝔻 : ∀ i h t s → DiagramComps i h t s → Con
Mᵒ : ∀ i h t s → Tel (𝔻 i h t s $ diagram-comps i h t s)

DiagramComps O h t s =
  Σ[ 𝔻  ː Con ]
  Σ[ Mᵒ ː Tel (𝔻 ∷ U) ]
  ( ∀ {j} (f : hom O j) → Sub (𝔻 ∷ U ++ₜₑₗ Mᵒ) (𝔻 ∷ U) )
DiagramComps (1+ i) O t s =
  Σ[ 𝔻'  ː Con ]
  Σ[ Mᵒ' ː Tel (𝔻' ∷ U) ]
  ( ∀ {j} (f : hom (1+ i) j)
    → let cf = count-factors (1+ i) O t s f
          sh = count-factors-gives-shape (1+ i) O t s f
      in Sub (𝔻' ∷ U ++ₜₑₗ Mᵒ') (𝔻' ∷ U ++ₜₑₗ {!Mᵒ j O cf sh!}) )
DiagramComps (1+ i) (1+ h) t s = {!!}

diagram-comps = {!!}

𝔻 = {!!}

Mᵒ = {!!}

-}
