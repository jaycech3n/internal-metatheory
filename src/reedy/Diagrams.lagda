A HoTT construction of Reedy fibrant diagrams
in contexts of a wild category with families
=============================================

**IMPORTANT! This version switches off termination checking.**

\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I
open import reedy.Cosieves I
open Cosieves-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

\end{code}


Preliminaries, Overview, and 𝔻 (context of diagram fillers)
-----------------------------------------------------------

The construction is a large mutually inductive definition with a large number of
components. The first two core ones are 𝔻 and Mᵒ:

• The context ( 𝔻 i ≡ A₀ : 𝔸₀, A₁ : 𝔸₁, ..., A(i - 1) : 𝔸(i - 1) ) consists of
  the "diagram fillers" up to level i, where 𝔸 k are the types of the fillers.

• Mᵒ (i, h, t) s : Tel 𝔻(h + 1) is the partial matching object of the diagram as
  a telescope.

\begin{code}

𝔻 : ℕ → Con
Mᵒ : (i h t : ℕ) → shape i h t → Tel (𝔻 (1+ h))

\end{code}

For readability, we immediately define a host of frequently used abbreviations.

\begin{code}

module Convenience where

  M : (i h t : ℕ) → shape i h t → Con
  M i h t s = close (Mᵒ i h t s)

  Mᵒᵗᵒᵗ : (i : ℕ) → Tel (𝔻 i)
  Mᵒᵗᵒᵗ O = •
  Mᵒᵗᵒᵗ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

  Mᵒᶠᵘˡˡ : (i h : ℕ) → Tel (𝔻 (1+ h))
  Mᵒᶠᵘˡˡ i h = Mᵒ i h full shp
    where
    full = hom-size i h
    shp = full-shape i h

  𝔸 : (i : ℕ) → Ty (𝔻 i)
  𝔸 i = Πₜₑₗ (Mᵒᵗᵒᵗ i) U

  A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ)
  A i = generic[ Mᵒᵗᵒᵗ i ]type

  M= : ∀ i h {t} {s} {t'} {s'} → t == t' → M i h t s == M i h t' s'
  M= i h {t} {s} {.t} {s'} idp = ap (M i h t) (shape-path s s')

  M=shape : ∀ {i h t} s s' → M i h t s == M i h t s'
  M=shape {i} {h} {t} s s' = ap (M i h t) (shape-path s s')

open Convenience

\end{code}

Then we can write down the definition of 𝔻:

\begin{code}

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

\end{code}

Note that we have not yet given the definition of Mᵒ. This definition uses the
functoriality of the partial matching object functor, which is given by the
additional components M⃗ (for the action on morphisms) and M⃗◦ (for functoriality
of M⃗).

\begin{code}

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f
        -- sh = count-factors-shape i h t s f
    in
    {cfs : shape j h cf}
  → Sub (M i h t s) (M j h cf cfs)

M⃗◦ :
  ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
  → let cf   = count-factors i h t s f
        p    = count-factors-comp i h t s f g -- Abstract over this too?
        cfs  = count-factors-shape i h t s f  -- And this too?
        cgs  = count-factors-shape j h cf cfs g
        cgfs = count-factors-shape i h t s (g ◦ f)
    in
    M⃗ j h cf cfs g {cgs} ◦ˢᵘᵇ M⃗ i h t s f
    ==
    idd (M= k h {s = cgfs} p) ◦ˢᵘᵇ M⃗ i h t s (g ◦ f)

\end{code}

Our encoding of linear cosieves as shapes does not present some important
equalities definitionally. Hence, when we define the functor M on shapes, we
need to transport along certain propositional equalities. One of these is the
following, used in the definition of Mᵒ, which needs to be defined mutually with
the other diagram components.

\begin{code}

M⁼= :
  ∀ i h t (s : shape i h (1+ t))
  → let prev = prev-shape s
        u = <-from-shape s
        [t] = #[ t ] i h u
        cf = count-factors i h t prev [t]
        sh = count-factors-shape i h t prev [t]
    in M h h cf sh == close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)

\end{code}


Partial matching objects: Mᵒ (object part)
------------------------------------------

Now we define the partial matching object functor. This will be done with a well
founded induction on shapes. For now, to more clearly present the intuitive
ideas and focus on the coherences before worrying about the fully correct
induction principle, we use pattern matching with the
\begin{code}
{-# TERMINATING #-}
\end{code}
pragma to (temporarily) circumvent when Agda doesn't see the well
foundedness.

The object part of the functor is Mᵒ.

\begin{code}

Mᵒ i h (1+ t) s =
  Mᵒ i h t prev ‣ A h [ idd eq ◦ˢᵘᵇ M⃗ i h t prev (#[ t ] i h u) ]
  where
  prev = prev-shape s
  u = <-from-shape s

  cfp = count-factors i h t prev (#[ t ] i h u)
  shp = count-factors-shape i h t prev (#[ t ] i h u)

  eq : M h h cfp shp == close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)
  eq = M⁼= i h t s

Mᵒ i (1+ h) O s = Mᵒᶠᵘˡˡ i h [ π (𝔸 (1+ h)) ]ₜₑₗ

Mᵒ i O O s = •

\end{code}

With the definition of Mᵒ in place we can prove M⁼=, by pattern matching on h.

\begin{code}

M⁼= i O t s =
  M O O cf sh =⟨ M= O O {s' = O≤ _} p ⟩
  M O O O (O≤ _) =⟨ idp ⟩
  close (Mᵒᵗᵒᵗ O [ π (𝔸 O) ]ₜₑₗ) =∎
  where
  prev = prev-shape s
  u = <-from-shape s
  [t] = #[ t ] i O u
  cf = count-factors i O t prev [t]
  sh = count-factors-shape i O t prev [t]

  p : cf == O
  p = count-factors-top-level i O t prev [t]

M⁼= i (1+ h) t s =
  M (1+ h) (1+ h) cf sh =⟨ M= (1+ h) (1+ h) {s' = O≤ _} p ⟩
  M (1+ h) (1+ h) O (O≤ _) =⟨ idp ⟩
  close (Mᵒᵗᵒᵗ (1+ h) [ π (𝔸 (1+ h)) ]ₜₑₗ) =∎
  where
  prev = prev-shape s
  u = <-from-shape s
  [t] = #[ t ] i (1+ h) u
  cf = count-factors i (1+ h) t prev [t]
  sh = count-factors-shape i (1+ h) t prev [t]

  p : cf == O
  p = count-factors-top-level i (1+ h) t prev [t]

\end{code}


Partial matching objects: M⃗ (morphism part)
--------------------------------------------

Now, the action M⃗ of the partial matching object on morphisms f.

The recursive definition of M⃗ in the (i, h, t+1) case requires its type to
compute to the appropriate value depending on whether or not f divides [t]ⁱₕ. To
actually allow this computation to occur, the type needs to expose an argument
of type (Dec (f ∣ #[ t ] i h u)).

\begin{code}

M⃗[_,_,1+_]-deptype :
  ∀ i h t (s : shape i h (1+ t)) {j} (f : hom i j)
  → (d : Dec (f ∣ #[ t ] i h (<-from-shape s)))
  → {cfs : shape j h (count-factors-aux i h t (<-from-shape s) f d)}
  → Type _
M⃗[ i , h ,1+ t ]-deptype s {j} f d {cfs} =
  Sub (M i h (1+ t) s)
      (M j h (count-factors-aux i h t (<-from-shape s) f d) cfs)

\end{code}

We also expose the discriminant in an auxiliary implementation of M⃗ (i, h, t+1);
this will be needed later.

\begin{code}

M⃗[_,_,1+_] :
  ∀ i h t s {j} (f : hom i j)
  → let u = <-from-shape s in
    (d : Dec (f ∣ #[ t ] i h u))
  → {cfs : shape j h (count-factors-aux i h t u f d)}
  → M⃗[ i , h ,1+ t ]-deptype s f d {cfs}
M⃗[ i , h ,1+ t ] s f (inl (g , _)) =
  {-idd (M=shape shp _) ◦ˢᵘᵇ-} M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, {!!}
  where
  prev = prev-shape s
  shp = count-factors-shape i h t prev f
M⃗[ i , h ,1+ t ] s f (inr no) = M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ])
  where prev = prev-shape s

\end{code}

Now we can wrap the above up into a definition of M⃗. We also define the
(i, h+1, 0) and (i, 0, 0) cases.

\begin{code}

M⃗ i h (1+ t) s f = M⃗[ i , h ,1+ t ] s f (f ∣? #[ t ] i h u)
  where u = <-from-shape s

M⃗ i (1+ h) O s {j} f =
  wkn-sub (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ j h)
    (idd eq ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f)
    {!commutation lemma; another component of the definition!}
    (𝔸 (1+ h))
  where
  fullᵢ = hom-size i h
  shpᵢ = full-shape i h

  cf = count-factors i h fullᵢ shpᵢ f
  sh = count-factors-shape i h fullᵢ shpᵢ f

  fullⱼ = hom-size j h
  shpⱼ = full-shape j h

  eq : M j h cf sh == M j h fullⱼ shpⱼ
  eq = M= j h (count-factors-full i h shpᵢ f)

M⃗ i O O s f = id

\end{code}


Partial matching objects: M⃗◦ (anafunctoriality)
------------------------------------------------

Again, in the (i, h, t+1) case we need the type of M⃗◦ to compute on whether or
not certain morphisms divide [t]ⁱₕ.

\begin{code}

M⃗◦[_,_,1+_]-deptype :
  ∀ i h t (s : shape i h (1+ t))
    {j} (f : hom i j) {k} (g : hom j k)
  → let u = <-from-shape s in
    Dec (g ◦ f ∣ #[ t ] i h u)
  → Dec (f ∣ #[ t ] i h u)
  → Type _
M⃗◦[ i , h ,1+ t ]-deptype s {j} f {k} g dgf df =
  let u    = <-from-shape s
      cf   = count-factors-aux i h t u f df
      p    = count-factors-comp-aux i h t u f g dgf df
      cfs  = count-factors-shape-aux i h t u f df
      cgs  = count-factors-shape j h cf cfs g
      cgfs = count-factors-shape-aux i h t u (g ◦ f) dgf
  in
  M⃗ j h cf cfs g {cgs} ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f df {cfs}
  ==
  idd (M= k h {s = cgfs} p) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s (g ◦ f) dgf

M⃗◦[_,_,1+_] :
  ∀ i h t (s : shape i h (1+ t))
    {j} (f : hom i j) {k} (g : hom j k)
  → let u = <-from-shape s in
    (dgf : Dec (g ◦ f ∣ #[ t ] i h u))
  → (df : Dec (f ∣ #[ t ] i h u))
  → M⃗◦[ i , h ,1+ t ]-deptype s f g dgf df

M⃗◦[ i , h ,1+ t ] s f g (inl yes[gf]) (inl yes[f]) = {!!}

M⃗◦[ i , h ,1+ t ] s f g (inl yes[gf]) (inr no[f]) =
  ⊥-rec $ no[f] $ comp-divides-first-divides i h t _ f g yes[gf]

M⃗◦[ i , h ,1+ t ] s {j} f {k} g dgf@(inr no[gf]) df@(inl yes[f]) =

  M⃗ j h (1+ cf) _ g ◦ˢᵘᵇ (M⃗ i h t (prev-shape s) f ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  {-
  =⟨ {!!} ⟩

  (M⃗ j h {!cf!} {!!} g ◦ˢᵘᵇ π (A h [ _ ]))
  ◦ˢᵘᵇ (M⃗ i h t (prev-shape s) f ◦ˢᵘᵇ π (A h [ _ ]) ,, _)
  -}

  =⟨ {!!} ⟩

  idd (M= k h p) ◦ˢᵘᵇ M⃗ i h t (prev-shape s) (g ◦ f) ◦ˢᵘᵇ π (A h [ _ ]) =∎

  where
  cf = count-factors i h t (prev-shape s) f
  p = count-factors-comp-aux i h t (<-from-shape s) f g dgf df

M⃗◦[ i , h ,1+ t ] s f g (inr no[gf]) (inr no[f]) =
  ! assˢᵘᵇ ∙ ap (_◦ˢᵘᵇ π (A h [ _ ])) (M⃗◦ i h t (prev-shape s) f g) ∙ assˢᵘᵇ

M⃗◦ i h (1+ t) s {j} f {k} g =
  M⃗◦[ i , h ,1+ t ] s f g
    (discrim i h t _ (g ◦ f))
    (discrim i h t _ f)

\end{code}

\begin{code}

M⃗◦ i (1+ h) O s f g = {!!}

M⃗◦ i O O s f {k} g =
  ap (_◦ˢᵘᵇ id) (ap (idd ∘ ap (M k O O)) (! $ prop-has-all-paths-idp _))

\end{code}
