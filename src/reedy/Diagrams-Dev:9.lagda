\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:9 {ℓₘᴵ ℓₒ ℓₘ}
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

record Match (b : ℕ) (bsh₀ : [ b ]BoundedShape) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)
𝔻 : (b : ℕ) → Con
MF : (b : ℕ) (bsh₀ : [ b ]BoundedShape) → Match b bsh₀

record Match b bsh₀ where
  eta-equality
  field Mᵒ : (bsh : [ b ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Tel (𝔻 b)

  M : (bsh : [ b ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Con
  M bsh w = close $ Mᵒ bsh w

  -- field Mᵒ-comp : ?

  field
    M⃗ :
      (bsh@(shape i h t s , u) : [ b ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)

𝔻 O = ◆
𝔻 (1+ O) = ◆ ∷ U
𝔻 (2+ b) = 𝔻 (1+ b) ∷ Πₜₑₗ (Match.Mᵒ (MF (1+ b) tot) tot (inl idp)) U
  where tot = total-shape-1+ b , ltS

module MF-def₁
  (bsh₀ : [ 1 ]BoundedShape)
  (ind : (bsh : [ 1 ]BoundedShape) → bsh <ₛᵇ bsh₀ → Match 1 bsh)
  where

  Mᵒ₁ : (bsh : [ 1 ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Tel (◆ ∷ U)
  Mᵒ₁ bsh (inr w) = Match.Mᵒ (ind bsh w) bsh (inl idp)
  Mᵒ₁ (shape i (1+ h) O s , ltSR ()) (inl p)
  Mᵒ₁ (shape i .O (1+ t) s , ltS) (inl idp) =
    pMᵒ ‣ generic-closed-type-in ◆ [ πₜₑₗ pMᵒ ]
    where
    pbsh = prev-bshape s ltS
    pMF = ind pbsh (on-𝑡 ltS)
    pMᵒ = Match.Mᵒ pMF pbsh (inl idp)
     -- ≡ Match.Mᵒ (ind pbsh (on-𝑡 ltS)) pbsh (inl idp)
     -- ≡ Mᵒ₁ pbsh' (inr (on-𝑡 ltS))
  Mᵒ₁ (shape i' O O s' , u) (inl p) = •

  M₁ : (bsh : [ 1 ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Con
  M₁ bsh w = close $ Mᵒ₁ bsh w

  -- compatibility :
  --   (bsh' : [ 1 ]BoundedShape) (v : bsh' <ₛᵇ bsh) (w : bsh' ≤ₛᵇ bsh)
  --   → ?
  --   → Mᵒ₁ bsh' (inr ) == Match.Mᵒ mf

  M⃗₁ :
    (bsh@(shape i h t s , u) : [ 1 ]BoundedShape)
    (w : bsh ≤ₛᵇ bsh₀)
    {j : ℕ} (f : hom i j)
    → let r = count-factors i h t s f in
      (rs : is-shape j h r)
    → let rsh = shape j h r rs , u in
      (rw : rsh ≤ₛᵇ bsh₀)
    → Sub (M₁ bsh w) (M₁ rsh rw)
  M⃗₁ bsh (inr w) f rs (inl x) = {!!}
  M⃗₁ bsh (inr w) f rs (inr rw) = {!Match.M⃗ (ind bsh w) bsh (inl idp) f rs (∙ₛ-≤ₛ (fst bsh) f)!}
  -- idd {!!} ◦ˢᵘᵇ Match.M⃗ (ind bsh w) bsh (inl idp) f rs (∙ₛ-≤ₛ (fst bsh) f)
  M⃗₁ bsh (inl idp) f rs rw = {!!}

open MF-def₁

MF-def :
  ∀ b (bsh₀ : [ 1+ b ]BoundedShape)
  → ((bsh : [ 1+ b ]BoundedShape) → bsh <ₛᵇ bsh₀ → Match (1+ b) bsh)
  → Match (1+ b) bsh₀
MF-def O bsh₀ ind = record { Mᵒ = Mᵒ₁ bsh₀ ind ; M⃗ = M⃗₁ bsh₀ ind }
MF-def (1+ b) bsh₀ ind = {!!}

MF (1+ b) = wf-ind (Match (1+ b)) (MF-def b) where
  open
    WellFoundedInduction [ 1+ b ]BoundedShape _<ₛᵇ_ (λ bsh₀ → <ₛᵇ-wf {_} {bsh₀})

\end{code}
