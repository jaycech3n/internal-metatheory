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
open Cosieves-IsStrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
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

Then we can formally write down the definition of 𝔻:

\begin{code}

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

\end{code}

Note that we have not yet given the definition of Mᵒ. This definition uses the
functoriality of the partial matching object functor, which is given by the
additional components M⃗ (for the action on morphisms) and M⃗∘ (for functoriality
of M⃗).

\begin{code}

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f
        sh = count-factors-shape i h t s f
    in Sub (M i h t s) (M j h cf sh)

M⃗◦ :
  ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
  → let cf = count-factors i h t s f
        sh = count-factors-shape i h t s f  -- Abstract over this too?
        p  = count-factors-comp i h t s f g -- And this too?
    in M⃗ j h cf sh g ◦ˢᵘᵇ M⃗ i h t s f == idd (M= k h p) ◦ˢᵘᵇ M⃗ i h t s (g ◦ f)

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
        u = S≤-< s
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
  u : t < hom-size i h
  u = S≤-< s

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
  u = S≤-< s
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
  u = S≤-< s
  [t] = #[ t ] i (1+ h) u
  cf = count-factors i (1+ h) t prev [t]
  sh = count-factors-shape i (1+ h) t prev [t]

  p : cf == O
  p = count-factors-top-level i (1+ h) t prev [t]

\end{code}

Partial matching objects: M⃗ (morphism part)
--------------------------------------------

Now, the action of the partial matching object on morphisms f.

In the (i, h, t+1) case, the recursive definition relies on certain types
computing to the appropriate things depending on whether or not f divides
[t]ⁱₕ. To actually allow this computation to occur, the relevant types need to
expose an argument of type (Dec (f ∣ #[ t ] i h u)).

\begin{code}

M⃗ i h (1+ t) s {j} f =
  depcase M⃗-deptype (f ∣? #[ t ] i h u)
    (λ (g , _) →
      idd (M=shape sh _) ◦ˢᵘᵇ M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,,
      {!!})
    (λ no →
      M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]))
  where
  u = S≤-< s

  M⃗-deptype : Dec (f ∣ #[ t ] i h u) → Type _
  M⃗-deptype d =
    Sub (M i h (1+ t) s)
        (M j h (count-factors[ i , h ,1+ t ] u f d)
          (count-factors-shape[ i , h ,1+ t ] u f d))

  prev = prev-shape s
  sh = count-factors-shape i h t prev f

\end{code}

The other cases for M⃗: (i, h+1, 0) and (i, 0, 0).

\begin{code}

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

Partial matching objects: M⃗∘ (anafunctoriality)
------------------------------------------------

As before, for the (i, h, t+1) case we need to compute on whether or not
(f ∣ [t]ⁱₕ).

\begin{code}

M⃗◦ i h (1+ t) s {j} f {k} g = {!!}

\end{code}

\begin{code}

M⃗◦ i (1+ h) O s f g = {!!}

M⃗◦ i O O s f {k} g =
  ap (_◦ˢᵘᵇ id) (ap (idd ∘ ap (M k O O)) (! $ prop-has-all-paths-idp _))

\end{code}
