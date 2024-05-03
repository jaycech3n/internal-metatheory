\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:5 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I

import reedy.CosieveShapes as Sh
open Sh I
open import reedy.ShapeOrder I
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

𝔻 : ℕ → Con

\end{code}

\begin{code}

Mᵒ : ∀ i h t s (ac : <ₛ-Accc i h t s) → Tel (𝔻 h)

module Convenience where
  M : ∀ i h t s → <ₛ-Accc i h t s → Con
  M i h t s ac = close (Mᵒ i h t s ac)

  -- Total matching context
  -- Abstract over accessibility witness?
  -- Mᵒᵗᵒᵗ[1+_] : ∀ i → <ₛ-Acc (total-shape-1+ i) → Tel (𝔻 i)
  -- Mᵒᵗᵒᵗ[1+ i ] = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-is-shape-1+ i)
  Mᵒᵗᵒᵗ[1+_] : ∀ i → Tel (𝔻 i)
  Mᵒᵗᵒᵗ[1+ i ] = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-is-shape-1+ i) <ₛ-is-wf

  𝔸[1+_] : ∀ i → Ty (𝔻 i)
  𝔸[1+ i ] = Πₜₑₗ Mᵒᵗᵒᵗ[1+ i ] U

  A[1+_] : ∀ i → Ty (𝔻 i ∷ 𝔸[1+ i ] ++ₜₑₗ Mᵒᵗᵒᵗ[1+ i ] [ π (𝔸[1+ i ]) ]ₜₑₗ)
  A[1+ i ] = generic-( Mᵒᵗᵒᵗ[1+ i ] )-indexed-type

  A₀ : Ty (◆ ∷ U)
  A₀ = generic-closed-type-in ◆

open Convenience

\end{code}

\begin{code}

𝔻 O = ◆ ∷ U
𝔻 (1+ i) = 𝔻 i ∷ 𝔸[1+ i ]

\end{code}

\begin{code}

M⃗ :
  ∀ i h t s (ac : <ₛ-Accc i h t s)
  → {j : ℕ} (f : hom i j)
  → let r = count-factors i h t s f in
    (rs : is-shape j h r)
  → (·-ac : <ₛ-Accc j h r rs)
  → Sub (M i h t s ac) (M j h r rs ·-ac)

-- M⃗◦ : ?

\end{code}

\begin{code}

Mᵒ i O O s ac = •
Mᵒ i (1+ h) O s ac = wkₜₑₗ $ Mᵒ i h (hom-size i h) (full-is-shape i h) <ₛ-is-wf

Mᵒ i O (1+ t) s (acc _ rec) =
  let
    pac = rec _ (on-𝑡 ltS)
    prev-Mᵒ = Mᵒ i O t ps pac
  in
    prev-Mᵒ ‣ A₀ [ πₜₑₗ prev-Mᵒ ]
  where
    ps = prev-is-shape s

Mᵒ i (1+ h) (1+ t) s (acc _ rec) =
  let
    pac = rec _ (on-𝑡 ltS)
    ·-ac = rec _ (on-𝑖 (hom-inverse _ _ [t]))
  in
    Mᵒ i (1+ h) t ps pac
      ‣ A[1+ h ] [ idd {!!} ◦ˢᵘᵇ M⃗ i (1+ h) t ps pac [t] rs ·-ac ]
  where
    ps = prev-is-shape s
    u = <-from-is-shape s
    [t] = #[ t ] i (1+ h) u
    rs = count-factors-is-shape i (1+ h) t ps [t]

\end{code}


Morphism action of matching object:

The recursive definition of M⃗ in the (i, h, t+1) case requires its type to
compute to the appropriate value depending on whether or not f divides [t]ⁱₕ. To
actually allow this computation to occur, the type needs to expose an argument
of type (Dec (f ∣ #[ t ] i h u)).

\begin{code}

M⃗[_,_,1+_]-deptype :
  ∀ i h t (s : is-shape i h (1+ t)) (ac : <ₛ-Accc i h (1+ t) s)
  → {j : ℕ} (f : hom i j)
  → let u = <-from-is-shape s in
    (d : Dec (f ∣ #[ t ] i h u))
  → let r = count-factors-aux i h t u f d in
    (rs : is-shape j h r) (·-ac : <ₛ-Accc j h r rs)
  → Type _
M⃗[ i , h ,1+ t ]-deptype s ac {j} f d rs ·-ac =
  Sub (M i h (1+ t) s ac)
      (M j h (count-factors-aux i h t (<-from-is-shape s) f d) rs ·-ac)

\end{code}

We also expose the discriminant in an auxiliary implementation of M⃗ (i, h, t+1);
this will be needed when defining M⃗◦.

\begin{code}

M⃗[_,_,1+_] :
  ∀ i h t s ac {j} (f : hom i j)
  → let u = <-from-is-shape s in
    (d : Dec (f ∣ #[ t ] i h u))
  → let r = count-factors-aux i h t u f d in
    (rs : is-shape j h r) (·-ac : <ₛ-Accc j h r rs)
  → M⃗[ i , h ,1+ t ]-deptype s ac f d rs ·-ac

M⃗[ i , O ,1+ t ] s (acc _ rec) f (inl yes) rs (acc _ ·-rec) =
  let
    pac = rec _ (on-𝑡 ltS)
    p·-rec = ·-rec _ (on-𝑡 ltS)
  in
    M⃗ i O t ps pac f prs p·-rec  ◦ˢᵘᵇ π _ ,, (υ _ ◂$ coeᵀᵐ {!!})
  where
    ps = prev-is-shape s
    prs = prev-is-shape rs
M⃗[ i , O ,1+ t ] s (acc _ rec) f (inr no) rs (acc _ ·-rec) = {!!}
M⃗[ i , 1+ h ,1+ t ] s ac f (inl yes) rs ·-ac = {!!}
M⃗[ i , 1+ h ,1+ t ] s ac f (inr no) rs ·-ac = {!!}

\end{code}

\begin{code}

M⃗ i O t s ac f rs ·-ac = {!!}
M⃗ i (1+ h) t s ac f rs ·-ac = {!!}

\end{code}
