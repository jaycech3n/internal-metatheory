\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:10 {ℓₘᴵ ℓₒ ℓₘ}
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

𝔻 : (b : ℕ) → Con
MF : (b : ℕ) (bsh₀ : [ b ]BoundedShape) → Σ[ M ﹕ Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) ] M
Mᵒ : (b : ℕ) (bsh₀ : [ b ]BoundedShape) → Tel (𝔻 b)

𝔻 O = ◆
𝔻 (1+ O) = ◆ ∷ U
𝔻 (2+ b) = 𝔻 (1+ b) ∷ {!!}

MF-def :
  ∀ b (bsh₀ : [ b ]BoundedShape)
  → ((bsh : [ b ]BoundedShape) → bsh <ₛᵇ bsh₀ → Σ[ M ﹕ Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) ] M)
  → Σ[ M ﹕ Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) ] M
MF-def b bsh₀ ind =
  ( -- Type
  Σ[ Mᵒ ﹕
    ((bsh : [ b ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Tel (𝔻 b)) ]
  Σ[ M⃗ ﹕
    ((bsh@(shape i h t s , u) : [ b ]BoundedShape)
    (w : bsh ≤ₛᵇ bsh₀)
    {j : ℕ} (f : hom i j)
    → let r = count-factors i h t s f in
      (rs : is-shape j h r)
    → let rsh = shape j h r rs , u in
      (rw : rsh ≤ₛᵇ bsh₀)
    → let M = λ bsh w → close (Mᵒ bsh w) in
      Sub (M bsh w) (M rsh rw)) ]
  ⊤
  ),
  ( -- Mᵒ
  λ{ bsh (inl idp) → {!!}
   ; bsh (inr w) → {!fst (ind bsh w)!}
  }),

  {!!} , {!!}

Mᵒ b bsh₀ = {! MF b bsh₀!}

MF (1+ b) = wf-ind (λ _ → Σ[ M ﹕ Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ) ] M) (MF-def (1+ b)) where
  open
    WellFoundedInduction [ 1+ b ]BoundedShape _<ₛᵇ_ (λ bsh → <ₛᵇ-wf {_} {bsh})

\end{code}

record Match b bsh where
  eta-equality
  field Mᵒ : (bsh' : [ b ]BoundedShape) → bsh' ≤ₛᵇ bsh → Tel (𝔻 b)

  M : (bsh' : [ b ]BoundedShape) → bsh' ≤ₛᵇ bsh → Con
  M bsh' w = close $ Mᵒ bsh' w

  field
    M⃗ :
      (bsh'@(shape i' h' t' s' , u') : [ b ]BoundedShape)
      (w : bsh' ≤ₛᵇ bsh)
      {j : ℕ} (f : hom i' j)
      → let r = count-factors i' h' t' s' f in
        (rs : is-shape j h' r)
      → let rsh = shape j h' r rs , u' in
        (rw : rsh ≤ₛᵇ bsh)
      → Sub (M bsh' w) (M rsh rw)

𝔻 O = ◆
𝔻 (1+ O) = ◆ ∷ U
𝔻 (2+ b) = 𝔻 (1+ b) ∷ Πₜₑₗ (Match.Mᵒ (MF (1+ b) tot) tot (inl idp)) U
  where tot = total-shape-1+ b , ltS

module MF-def₁
  (bsh : [ 1 ]BoundedShape)
  (ind : (bsh' : [ 1 ]BoundedShape) → bsh' <ₛᵇ bsh → Match 1 bsh')
  where

  Mᵒ₁ : (bsh' : [ 1 ]BoundedShape) → bsh' ≤ₛᵇ bsh → Tel (◆ ∷ U)
  Mᵒ₁ bsh' (inr w) = Match.Mᵒ (ind bsh' w) bsh' (inl idp)
  Mᵒ₁ (shape i' (1+ h') O s' , ltSR ()) (inl p)
  Mᵒ₁ (shape i' .O (1+ t') s' , ltS) (inl idp) =
    pMᵒ ‣ generic-closed-type-in ◆ [ πₜₑₗ pMᵒ ]
    where
    pbsh' = prev-bshape s' ltS
    pMF = ind pbsh' (on-𝑡 ltS)
    pMᵒ = Match.Mᵒ pMF pbsh' (inl idp)
     -- ≡ Match.Mᵒ (ind pbsh' (on-𝑡 ltS)) pbsh' (inl idp)
     -- ≡ Mᵒ₁ pbsh' (inr (on-𝑡 ltS))
  Mᵒ₁ (shape i' O O s' , u) (inl p) = •

  M₁ : (bsh' : [ 1 ]BoundedShape) → bsh' ≤ₛᵇ bsh → Con
  M₁ bsh' w = close $ Mᵒ₁ bsh' w

  -- compatibility :
  --   (bsh' : [ 1 ]BoundedShape) (v : bsh' <ₛᵇ bsh) (w : bsh' ≤ₛᵇ bsh)
  --   → ?
  --   → Mᵒ₁ bsh' (inr ) == Match.Mᵒ mf

  M⃗₁ :
    (bsh'@(shape i' h' t' s' , u') : [ 1 ]BoundedShape)
    (w : bsh' ≤ₛᵇ bsh)
    {j : ℕ} (f : hom i' j)
    → let r = count-factors i' h' t' s' f in
      (rs : is-shape j h' r)
    → let rsh = shape j h' r rs , u' in
      (rw : rsh ≤ₛᵇ bsh)
    → Sub (M₁ bsh' w) (M₁ rsh rw)
  M⃗₁ bsh' (inr w) f rs rw = idd {!!} ◦ˢᵘᵇ Match.M⃗ (ind bsh' w) bsh' (inl idp) f rs (∙ₛ-≤ₛ (fst bsh') f)
  M⃗₁ bsh' (inl idp) f rs rw = {!!}

open MF-def₁

MF-def :
  ∀ b (bsh : [ 1+ b ]BoundedShape)
  → ((bsh' : [ 1+ b ]BoundedShape) → bsh' <ₛᵇ bsh → Match (1+ b) bsh')
  → Match (1+ b) bsh
MF-def O bsh ind = record { Mᵒ = Mᵒ₁ bsh ind ; M⃗ = M⃗₁ bsh ind }
MF-def (1+ b) bsh ind = {!!}

MF (1+ b) = wf-ind (Match (1+ b)) (MF-def b) where
  open
    WellFoundedInduction [ 1+ b ]BoundedShape _<ₛᵇ_ (λ bsh → <ₛᵇ-wf {_} {bsh})
