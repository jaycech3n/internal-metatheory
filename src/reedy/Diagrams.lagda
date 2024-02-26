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


Preliminaries, Overview, and Declarations
-----------------------------------------

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

  M=shape : ∀ {i h t} s s' → M i h t s == M i h t s'
  M=shape {i} {h} {t} s s' = ap (M i h t) (shape-path s s')

  M= : ∀ i h {t} s {t'} s' → t == t' → M i h t s == M i h t' s'
  M= i h {t} s {.t} s' idp = M=shape s s'

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
  → let cf = count-factors i h t s f in
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
    idd (M= k h cgfs _ p) ◦ˢᵘᵇ M⃗ i h t s (g ◦ f)

\end{code}

Our construction does not satisfy some desired equalities definitionally, so we
need to transport along certain propositional equalities.

One of these is the following equality Mᵗᵒᵗ=. Morally this is just reflexivity,
but for computational reasons it needs to be defined mutually with the other
diagram components.

\begin{code}

Mᵗᵒᵗ= : ∀ i → M i i O (O≤ _) == close (Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ)

\end{code}

We also define, for better abstraction, abbreviations M-improper= and
M⃗[ i , h ][ t ], and require them to satisfy a certain composition rule which
also needs to be proved mutually with the other components.

\begin{code}

M-improper= :
  ∀ i h t (s : shape i h (1+ t))
  → let [t] = #[ t ] i h (<-from-shape s)
        s' = prev-shape s
        cf = count-factors i h t s' [t]
        sh = count-factors-shape i h t s' [t]
    in M h h cf sh == close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)
M-improper= i h t s =
  M= h h _ _ p ∙ Mᵗᵒᵗ= h
  where
  s' = prev-shape s
  [t] = #[ t ] i h (<-from-shape s)
  cf = count-factors i h t s' [t]

  p : cf == O
  p = count-factors-top-level i h t s' [t]

M⃗[_,_][_] :
  ∀ i h t (s : shape i h (1+ t))
  → Sub (M i h t (prev-shape s)) (close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ))
M⃗[ i , h ][ t ] s =
  idd (M-improper= i h t s) ◦ˢᵘᵇ M⃗ i h t (prev-shape s) [t]
  where
  [t] = #[ t ] i h (<-from-shape s)

need :
  ∀ i h t (s : shape i h (1+ t)) {j} (f : hom i j)
  → let s' = prev-shape s
        u = <-from-shape s
        cf = count-factors i h t s' f
    in
    (d : f ∣ #[ t ] i h u)
   → (cfs : shape j h (1+ cf))
  → idd (M-improper= j h cf cfs) ◦ˢᵘᵇ
      M⃗ j h cf (prev-shape cfs) (#[ cf ] j h (<-from-shape cfs))
        ◦ˢᵘᵇ M⃗ i h t s' f
    == M⃗[ i , h ][ t ] s

need i h O s f d = {!!}
need i h (1+ t) s f d = {!!}

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
pragma to (temporarily) circumvent when Agda doesn't see the well foundedness.

The object part of the functor is Mᵒ.

\begin{code}

Mᵒ i h (1+ t) s = Mᵒ i h t (prev-shape s) ‣ A h [ M⃗[ i , h ][ t ] s ]
Mᵒ i (1+ h) O s = Mᵒᶠᵘˡˡ i h [ π (𝔸 (1+ h)) ]ₜₑₗ
Mᵒ i O O s = •

\end{code}

With the definition of Mᵒ in place we can now prove Mᵗᵒᵗ= by induction on i.

\begin{code}

Mᵗᵒᵗ= O = idp
Mᵗᵒᵗ= (1+ _) = idp

-- This works too, of course.
-- Mᵗᵒᵗ= =
--   ℕ-ind
--     (λ i → M i i O (O≤ $ hom-size i i) == close (Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ))
--     idp
--     (λ _ _ → idp)

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
this will be needed when defining M⃗◦.

\begin{code}

M⃗[_,_,1+_] :
  ∀ i h t s {j} (f : hom i j)
  → let u = <-from-shape s in
    (d : Dec (f ∣ #[ t ] i h u))
  → {cfs : shape j h (count-factors-aux i h t u f d)}
  → M⃗[ i , h ,1+ t ]-deptype s f d {cfs}

M⃗[ i , h ,1+ t ] s {j} f d@(inl yes) {cfs} =
  M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, (υ _ ◂$ transp Tm q)
  where
  prev = prev-shape s
  cf = count-factors i h t prev f
  prev-cfs = prev-shape cfs
  u = <-from-shape cfs
  [cf] = #[ cf ] j h u

  p : M⃗[ j , h ][ cf ] cfs ◦ˢᵘᵇ M⃗ i h t prev f == M⃗[ i , h ][ t ] s
  p =
    M⃗[ j , h ][ cf ] cfs ◦ˢᵘᵇ M⃗ i h t prev f
      =⟨ assˢᵘᵇ ⟩
    idd (M-improper= j h cf cfs)
    ◦ˢᵘᵇ (M⃗ j h cf prev-cfs [cf] ◦ˢᵘᵇ M⃗ i h t prev f)
      =⟨ need i h t s f yes cfs ⟩
    M⃗[ i , h ][ t ] s
      =∎

  q : A h [ M⃗[ i , h ][ t ] s ] [ π _ ]
      ==
      A h [ M⃗[ j , h ][ cf ] cfs ] [ M⃗ i h t prev f ◦ˢᵘᵇ π _ ]
  q = ap (_[ π _ ]) ([= ! p ] ∙ [◦]) ∙ ! [◦]

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
  eq = M= j h _ _ (count-factors-full i h shpᵢ f)

M⃗ i O O s f = id

\end{code}

Another equality we need to use is M⃗rec=.

\begin{code}

idd◦M⃗= :
  ∀ i h t (s : shape i h (1+ t))
  → ∀ {j} (f : hom i j)
  → (d : Dec (f ∣ #[ t ] i h (<-from-shape s)))
  → let c = count-factors-aux i h t (<-from-shape s) f d in
    (s₀ s₁ : shape j h c)
  → (p q : c == c)
  → idd (M= j h s₀ s₁ p) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d {s₀} ==
    idd (M= j h s₁ s₁ q) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d {s₁}
idd◦M⃗= i h t s {j} f d s₀ s₁ p q =
  ap (λ (sₓ , e) → idd (M= j h sₓ s₁ e) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f d {sₓ})
     (pair×=
       (prop-path shape-is-prop s₀ s₁)
       (prop-path has-level-apply-instance p q))

abstract
  M⃗rec= :
    ∀ i h t (s : shape i h (1+ t)) {j} (f : hom i j)
    → (no : ¬ (f ∣ #[ t ] i h (<-from-shape s)))
    → let prev = prev-shape s
          cf = count-factors i h (1+ t) s f
          cfp = count-factors i h t prev f
          p = count-factors-not-divisible i h t s f no
      in
      (cfs : shape j h cf) (cfps : shape j h cfp)
    → M⃗ i h (1+ t) s f {cfs} ==
      idd (M= j h cfps cfs (! p)) ◦ˢᵘᵇ M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ])
  M⃗rec= i h t s {j} f no cfs cfps with discrim i h t (<-from-shape s) f
  ... | inl yes = ⊥-rec $ no yes
  ... | inr no' =
        ! $
        idd (M= j h cfps cfs p)
          ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') {cfps}
        =⟨ idd◦M⃗= i h t s f (inr no') cfps cfs p idp ⟩
        idd (M= j h cfs cfs idp) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') {cfs}
        =⟨ ap
            (λ ◻ →
              idd (ap (M j h _) ◻) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') {cfs})
            (prop-path shape-id-is-prop (shape-path cfs cfs) idp)
        ⟩
        id ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f (inr no') {cfs}
        =⟨ idl _ ⟩
        M⃗[ i , h ,1+ t ] s f (inr no') {cfs}
        =∎
        where
        p : count-factors-aux i h t (<-from-shape s) f (inr no') ==
            count-factors-aux i h t (<-from-shape s) f (inr no')
        p = ! $ count-factors-not-divisible-aux i h t (<-from-shape s)
                  f (inr no') no


\end{code}


Partial matching objects: M⃗◦ (functoriality)
---------------------------------------------

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
      cfs  = count-factors-shape-aux i h t u f df
      cgs  = count-factors-shape j h cf cfs g
      cgfs = count-factors-shape-aux i h t u (g ◦ f) dgf
      p    = count-factors-comp-aux i h t u f g dgf df
  in
  M⃗ j h cf cfs g {cgs} ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s f df {cfs}
  ==
  idd (M= k h cgfs _ p) ◦ˢᵘᵇ M⃗[ i , h ,1+ t ] s (g ◦ f) dgf

M⃗◦[_,_,1+_] :
  ∀ i h t (s : shape i h (1+ t))
    {j} (f : hom i j) {k} (g : hom j k)
  → let u = <-from-shape s in
    (dgf : Dec (g ◦ f ∣ #[ t ] i h u))
  → (df : Dec (f ∣ #[ t ] i h u))
  → M⃗◦[ i , h ,1+ t ]-deptype s f g dgf df

M⃗◦[ i , h ,1+ t ] s {j} f {k} g (inl yes[gf]) (inl yes[f]) =

  M⃗ j h (1+ cf) _ g ◦ˢᵘᵇ (M⃗ i h t (prev-shape s) f ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ {!!} ⟩

  idd (M= k h ? ? {!!}) ◦ˢᵘᵇ {!!} =∎

  where
  cf = count-factors i h t (prev-shape s) f

M⃗◦[ i , h ,1+ t ] s f g (inl yes[gf]) (inr no[f]) =
  ⊥-rec $ no[f] $ comp-divides-first-divides i h t _ f g yes[gf]

M⃗◦[ i , h ,1+ t ] s {j} f {k} g dgf@(inr no[gf]) df@(inl yes[f]) =

  M⃗ j h (1+ cf) cfs g ◦ˢᵘᵇ (M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ ap (_◦ˢᵘᵇ (M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, _))
        (M⃗rec= j h cf cfs g no[g] cgs cgs') ⟩

  (idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ M⃗ j h cf (prev-shape cfs) g
    ◦ˢᵘᵇ π (A h [ _ ]))
  ◦ˢᵘᵇ (M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ assˢᵘᵇ ∙ ap (idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ_) assˢᵘᵇ ⟩

  idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ M⃗ j h cf (prev-shape cfs) g
  ◦ˢᵘᵇ π (A h [ _ ]) ◦ˢᵘᵇ (M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, _)

  =⟨ βπ
   |in-ctx (λ ◻ →
     idd (M= k h cgs' cgs (! q))
     ◦ˢᵘᵇ M⃗ j h cf (prev-shape cfs) g
     ◦ˢᵘᵇ ◻) ⟩

  idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ M⃗ j h cf (prev-shape cfs) g
  ◦ˢᵘᵇ M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ ap (idd (M= k h cgs' cgs (! q)) ◦ˢᵘᵇ_) (! assˢᵘᵇ) ∙ ! assˢᵘᵇ ⟩

  (idd (M= k h cgs' cgs (! q))
    ◦ˢᵘᵇ M⃗ j h cf (prev-shape cfs) g {cgs'} ◦ˢᵘᵇ M⃗ i h t prev f)
  ◦ˢᵘᵇ π (A h [ _ ])

  -- =⟨ M⃗◦ i h t prev f g
  --  |in-ctx (λ ◻ →
  --    (idd (M= k h cgs' cgs (! q))
  --      ◦ˢᵘᵇ ◻)
  --    ◦ˢᵘᵇ π (A h [ _ ])) ⟩

  =⟨ {!!} ⟩

  (idd (M= k h cgs' cgs (! q))
    ◦ˢᵘᵇ idd (M= k h cgfs cgs' (r ∙ e)) ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) {cgfs})
  ◦ˢᵘᵇ π (A h [ _ ])

  =⟨ {!!} ⟩

  idd (M= k h _ _ p) ◦ˢᵘᵇ M⃗ i h t prev (g ◦ f) ◦ˢᵘᵇ π (A h [ _ ]) =∎

  where
  prev = prev-shape s
  u = <-from-shape s
  no[g] = comp-divides-contra i h t u f g yes[f] no[gf]
  dg = inr no[g]

  cf = count-factors i h t prev f
  cfs = count-factors-shape-aux i h t u f df

  cgs = count-factors-shape j h (1+ cf) cfs g
  cgs' = count-factors-shape-aux j h cf (<-from-shape cfs) g dg

  cgfs = count-factors-shape i h t prev (g ◦ f)

  q = count-factors-not-divisible j h cf cfs g no[g]
  p = count-factors-comp-aux i h t u f g dgf df
  r = count-factors-comp i h t prev f g
  e = ap (λ ◻ → count-factors j h cf ◻ g) (shape-path _ _)

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
