{-# OPTIONS --without-K --rewriting --experimental-lossy-unification #-}

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.ContextDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves I
open SuitableSemicategory I
open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr

record Components (n : ℕ) : Type (ℓₒ l⊔ ℓₘ) where
  field
    SCT : Con
    F : Ty SCT
    M : (i h t : ℕ) → is-shape i h t → h < n → Con
    -- M⃗
    Π′⋆ :
      (i h t h' t' : ℕ)
      (iS : is-shape i h t) (iS' : is-shape i h' t')
      (u : h < n) (u' : h' < n)
      → (h' , t') ≤ₛ+ (h , t)
      → Ty (M i h t iS u) → Ty (M i h' t' iS' u')
    -- Projection from larger to smaller matching context drops components
    π⋆ᴹ : ∀ i {h t h' t'} iS iS' u u'
      → (h' , t') ≤ₛ+ (h , t)
      → Sub (M i h t iS u) (M i h' t' iS' u')

open Components

module InnerInduction (n : ℕ) (at-n : Components n) where
  -- Given components of the diagram at level n, define the components at level (n+1)
  -- by induction on (i, h, t), etc.

  SCT+ : Con
  M+ : (i h t : ℕ) → is-shape i h t → h < 1+ n → Con
  Π′⋆+ :
    (i h t h' t' : ℕ)
    (iS : is-shape i h t) (iS' : is-shape i h' t')
    (u : h < 1+ n) (u' : h' < 1+ n)
    → (h' , t') ≤ₛ+ (h , t)
    → Ty (M+ i h t iS u) → Ty (M+ i h' t' iS' u')
  F+ : Ty SCT+

  SCT+ = SCT at-n ∷ F at-n

  M+ i h (1+ t) iS u
    = M+ i h t iS' u ∷ {!!}
    where iS' = shapeₜ↓ iS
  M+ i (1+ h) O iS u
    = M+ i h (hom-size i h) iS' u'
    where
    iS' = shapeₕ↓ iS
    u' = S<-< u
  M+ i O O iS u = SCT+

  Π′⋆+ i h t .h .t iS iS' u u' done A = {!A!}
  Π′⋆+ i h t h' t' iS iS' u u' (on-height w) A = {!!}
  Π′⋆+ i h t .h t' iS iS' u u' (on-width w) A
    = Π′ _ (Π′⋆+ i h t h (1+ t') iS iS'' u u' w A)
      ◂$ transp-shape (λ ◻ → Ty (M+ i h t' ◻ u')) iS'
    where
    aux1 : 1+ t' ≤ t
    aux1 = ≤ₛ+-width-≤ w
    aux2 : 1+ t' ≤ hom-size i h
    aux2 = ≤-trans aux1 (tcond iS)
    iS'' : is-shape i h (1+ t')
    iS'' = shape-conds (hcond iS') aux2

  F+ = Π′⋆+ (1+ n) n (hom-size (1+ n) n) O O iS iS' u u' w U
    where
    iS = full-shape-1+ n
    iS' = empty-shape (1+ n)
    u = ltS
    u' = O<S n
    w = ≤ₛ-≤ₛ+ _ _ (O≤ₛ n (hom-size (1+ n) n))

comps : (n : ℕ) → Components n
ind : (n : ℕ) → Components n → Components (1+ n)

comps n = {!!}
ind n = {!!}
