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


-- record MatchingComps (i : ℕ) (D : ℕ → Con) : Type ? where
--   Mᵒ : (h t : ℕ) → shape i h t → 



{- Attempt 4 ====

record DiagComps (i : ℕ) : Type (lsuc (ℓₘᴵ ∪ ℓₘ ∪ ℓₒ)) where
  -- constructor 𝔻=_𝕄=_
  field
    𝔻 : Con
    𝕄 : (h t : ℕ) (s : shape i h t)
        → Σ[ MatchingComps ː Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) ] MatchingComps

open DiagComps

Diag : (i : ℕ) → DiagComps i
Mᵒₜₒₜ : ∀ i → DiagComps i → Tel (𝔻 (Diag i))

Diag O = record { 𝔻 = 𝔻₀ ; 𝕄 = 𝕄₀ } where
  𝔻₀ = ◆

  𝕄₀ : ∀ h t → shape O h t → Σ[ MatchingComps ː Type _ ] MatchingComps
  𝕄₀ h t s = Lift {j = ℓₘᴵ ∪ ℓₒ ∪ ℓₘ} (Tel (𝔻₀ ∷ U)) , lift •

Diag (1+ i) = record { 𝔻 = 𝔻[i+1] ; 𝕄 = 𝕄[1+i] } where
  î = Diag i
  𝔻[i+1] = 𝔻 î ∷ Πₜₑₗ (Mᵒₜₒₜ _ î) U

  𝕄[1+i] : ∀ h t → shape (1+ i) h t → Σ[ MatchingComps ː Type _ ] MatchingComps
  𝕄[1+i] h (1+ t) s = {!!}
  𝕄[1+i] (1+ h) O s = {!!}
  𝕄[1+i] O O s = {!!}

Mᵒₜₒₜ O _ = •
Mᵒₜₒₜ (1+ i) diag = {!snd $ 𝕄 diag i (hom-size (1+ i) i) (total-shape-1+ i)!}
-}


{- Attempt 3 ====

Diag O = record { 𝔻 = ◆ ; 𝕄 = λ _ _ _ → Lift ⊤ , ✶ }
Diag 1 = record { 𝔻 = ◆ ∷ U ; 𝕄 = 𝕄₁ }
  where
  𝕄₁ : (h t : ℕ) → shape 1 h t
    → Σ[ MatchingFunctorComps ː Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) ] MatchingFunctorComps
  𝕄₁ h (1+ t) s = {!!}
  𝕄₁ (1+ h) O s = {!!}
  𝕄₁ O O s =
    (Σ[ Mᵒ[1,0,0] ː Tel {!!} ]
    {!!})
    , {- Mᵒ[1,0,0] : Tel (D 0 ∷ 𝔸 0) -}
      •
    , {- M⃗[1,0,0] : {j} (f : hom 1 j) → Sub (D 0 ∷ 𝔸 0 ++ₜₑₗ Mᵒ[1,0,0]) ()-}
      {!!}
    , {!!}

Diag (2+ i) = {!!}
-}


{- Attempt 2 ====

Diag : (i h t : ℕ) (s : shape i h t)
  → Σ[ Comps ː Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) ] -- types of the diagram components
    Comps -- actual diagram components

Diag O h t s =
  ( Σ[ 𝔻' ː Con ]
    Σ[ Mᵒ' ː Tel (𝔻' ∷ U) ]
    ( ∀ {j} (f : hom O j) → Sub (𝔻' ∷ U ++ₜₑₗ Mᵒ') (𝔻' ∷ U) ) )
  ,
  ◆ , • , λ _ → id
Diag (1+ i) h (1+ t) s = {!!}
Diag (1+ i) (1+ h) O s = {!!}
Diag (1+ i) O O s =
  ( Σ[ 𝔻 ː Con ]
    Σ[ Mᵒ' ː Tel {!!} ]
    ( {!∀ {j} (f : hom i j)
      → Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ i h t s) (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ j h cf sh)!} ) )
  ,
  {!!}
-}


{- Attempt 1 ====

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
