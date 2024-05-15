\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=10 -vterm.type:60 #-}

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

module Abbreviations where
  -- None of these should be defined by pattern matching.

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

  M-𝑡= :
    ∀ i h t t' {s s'} {ac ac'}
    → (p : t == t')
    → close (Mᵒ i h t s ac) == close (Mᵒ i h t' s' ac')
  M-𝑡= i h t t' p =
    ap↓2 {A = Shape} {B = <ₛ-Acc}
      (λ (shape i h t s) ac → close (Mᵒ i h t s ac))
      (ap↓2 (shape i h) p (shape=↓ i h _))
      (<ₛ-Acc=↓ _)

open Abbreviations

\end{code}

\begin{code}

𝔻 O = ◆ ∷ U
𝔻 (1+ i) = 𝔻 i ∷ 𝔸[1+ i ]

\end{code}

Morphism action of the matching object.

\begin{code}

M⃗ :
  ∀ i h t s (ac : <ₛ-Accc i h t s)
  → {j : ℕ} (f : hom i j)
  → let r = count-factors i h t s f in
    (rs : is-shape j h r)
  → (rac : <ₛ-Accc j h r rs)
  → Sub (close $ Mᵒ i h t s ac) (close $ Mᵒ j h r rs rac)

\end{code}

\begin{code}

Mᵒ i O O s ac = •
Mᵒ i (1+ h) O s ac = wkₜₑₗ $ Mᵒ i h (hom-size i h) (full-is-shape i h) <ₛ-is-wf

Mᵒ i O (1+ t) s (acc _ rec) =
  let
    ps = prev-is-shape s
    pac = rec _ (on-𝑡 ltS)
    pMᵒ = Mᵒ i O t ps pac
  in
    pMᵒ ‣ A₀ [ πₜₑₗ pMᵒ ]
  -- where
  --   ps = prev-is-shape s

Mᵒ i (1+ h) (1+ t) s (acc _ rec) =
  let
    pac = rec _ (on-𝑡 ltS)
    rac = rec _ (on-𝑖 (hom-inverse _ _ [t]))
  in
    Mᵒ i (1+ h) t ps pac
      ‣ A[1+ h ] [ idd {!!} ◦ˢᵘᵇ M⃗ i (1+ h) t ps pac [t] rs rac ]
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
    (rs : is-shape j h r) (rac : <ₛ-Accc j h r rs)
  → Type _
M⃗[ i , h ,1+ t ]-deptype s ac {j} f d rs rac =
  Sub (close $ Mᵒ i h (1+ t) s ac)
      (close $ Mᵒ j h (count-factors-aux i h t (<-from-is-shape s) f d) rs rac)

\end{code}

We also expose the discriminant in an auxiliary implementation of M⃗ (i, h, t+1);
this will be needed when defining M⃗◦.

\begin{code}

M⃗[_,_,1+_] :
  ∀ i h t s ac {j} (f : hom i j)
  → let u = <-from-is-shape s in
    (d : Dec (f ∣ #[ t ] i h u))
  → let r = count-factors-aux i h t u f d in
    (rs : is-shape j h r) (rac : <ₛ-Accc j h r rs)
  → M⃗[ i , h ,1+ t ]-deptype s ac f d rs rac

\end{code}

We need a few equalities to hold. These must be proved simultaneously with the
main components. Chief among them is functoriality of the matching object.

\begin{code}

M⃗◦ :
  ∀ i h t s ac
  → {j : ℕ} (f : hom i j) {k : ℕ} (g : hom j k)
  → let rf = count-factors i h t s f in
    (rfs : is-shape j h rf) (rfac : <ₛ-Accc j h rf rfs)
  → let rg = count-factors j h rf rfs g in
    (rgs : is-shape k h rg) (rgac : <ₛ-Accc k h rg rgs)
  → let rgf = count-factors i h t s (g ◦ f) in
    (rgfs : is-shape k h rgf) (rgfac : <ₛ-Accc k h rgf rgfs)
  → idd (M-𝑡= k h _ _ (count-factors-comp i h t s f g rfs))
      ◦ˢᵘᵇ M⃗ i h t s ac (g ◦ f) rgfs rgfac
    == M⃗ j h rf rfs rfac g rgs rgac ◦ˢᵘᵇ M⃗ i h t s ac f rfs rfac

\end{code}

Also need the following commutation lemmas:

     M (i, 0, t) -----> M (j, 0, count-factors (i, 0, t) f)
              ╲           ╱
               ╲  comm₀  ╱
                ╲       ╱
                 v     v  πₜₑₗ
                   𝔻 0

\begin{code}

comm₀ :
  ∀ i t (s : is-shape i O t) (ac : <ₛ-Accc i O t s)
  → {j : ℕ} (f : hom i j)
  → let rf = count-factors i O t s f in
    (rfs : is-shape j O rf) (rfac : <ₛ-Accc j O rf rfs)
  → πₜₑₗ (Mᵒ j O rf rfs rfac) ◦ˢᵘᵇ M⃗ i O t s ac f rfs rfac
    == πₜₑₗ (Mᵒ i O t s ac)

\end{code}

\begin{code}

M⃗[ i , O ,1+ t ] s (acc _ rec) {j} f d@(inl yes) rs (acc _ rrec) =
  let
    ps = prev-is-shape s
    prs = prev-is-shape rs

    prf = count-factors i O t ps f

    pac = rec _ (on-𝑡 ltS)
    pMᵒ = Mᵒ i O t ps pac

    prac = rrec _ (on-𝑡 ltS)
    prMᵒ = Mᵒ j O prf prs prac

    {- For termination checking reasons pac and prac can't be in a where block,
       so neither can any terms depending on them. But the type of p below is

       p : A₀ [ πₜₑₗ pMᵒ ] [ π (A₀ [ πₜₑₗ pMᵒ ]) ]
           ==
           A₀ [ πₜₑₗ prMᵒ ] [ M⃗ i O t ps pac f prs prac ◦ˢᵘᵇ π (A₀ [ πₜₑₗ pMᵒ ]) ]
    -}
    p = ap _[ π (A₀ [ πₜₑₗ pMᵒ ])] (([= ! (comm₀ i t ps pac f prs prac) ]) ∙ ([◦] {A = A₀})) ∙ ![◦]
  in
    M⃗ i O t ps pac f prs prac  ◦ˢᵘᵇ π _ ,, (υ _ ◂$ coeᵀᵐ p)
  where
    -- ps = prev-is-shape s
    -- prs = prev-is-shape rs

    -- prf = count-factors i O t ps f

M⃗[ i , O ,1+ t ] s (acc _ rec) f (inr no) rs (acc _ rrec) = {!!}
M⃗[ i , 1+ h ,1+ t ] s ac f (inl yes) rs rac = {!!}
M⃗[ i , 1+ h ,1+ t ] s ac f (inr no) rs rac = {!!}

\end{code}

\begin{code}

M⃗ i O O s ac f rs rac = id
M⃗ i O (1+ t) s ac f rs rac =
  M⃗[ i , O ,1+ t ] s ac f (discrim i O t u f) rs rac
  where u = <-from-is-shape s
M⃗ i (1+ h) O s ac f rs rac = {!!}
M⃗ i (1+ h) (1+ t) s ac f rs rac = {!!}

\end{code}

Proof of equations:

\begin{code}

comm₀-aux :
  ∀ i t (s : is-shape i O (1+ t))
  → let u = <-from-is-shape s in
    (ac : <ₛ-Accc i O (1+ t) s)
  → {j : ℕ} (f : hom i j)
  → (d : Dec (f ∣ #[ t ] i O u))
  → let rf = count-factors-aux i O t u f d in
    (rfs : is-shape j O rf) (rfac : <ₛ-Accc j O rf rfs)
  → πₜₑₗ (Mᵒ j O rf rfs rfac) ◦ˢᵘᵇ M⃗[ i , O ,1+ t ] s ac f d rfs rfac
    == πₜₑₗ (Mᵒ i O (1+ t) s ac)

comm₀-aux i t s (acc _ rec) f (inl yes) rfs (acc _ rrec) = assˢᵘᵇ ∙ {!!} -- _ =⟨ {!!} ⟩ _ =∎
comm₀-aux i t s (acc _ rec) f (inr no) rfs (acc _ rrec) = {!!}

comm₀ i O s (acc _ rec) f rfs (acc _ rrec) = idr (πₜₑₗ •)
comm₀ i (1+ t) s (acc _ rec) f rfs (acc _ rrec) =
  comm₀-aux i t s (acc (shape i O (1+ t) s) rec) f (discrim i O t (<-from-is-shape s) f) rfs (acc _ rrec)

\end{code}

\begin{code}

M⃗◦ = {!!}

\end{code}
