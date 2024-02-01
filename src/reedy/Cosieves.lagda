Cosieves in countably simple semicategories
===========================================

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.Cosieves {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I

\end{code}


Shapes of linear cosieves
-------------------------

\begin{code}

shape : ℕ → ℕ → ℕ → Type₀
shape i h t = t ≤ hom-size i h

prev-shape : ∀ {i h t} → shape i h (1+ t) → shape i h t
prev-shape = S≤-≤

full-shape : ∀ i h → shape i h (hom-size i h)
full-shape i h = lteE

total-shape-1+ : ∀ i → shape (1+ i) i (hom-size (1+ i) i)
total-shape-1+ i = full-shape (1+ i) i

<-to-shape : ∀ {i h t} → t < hom-size i h → shape i h t
<-to-shape = inr

<-from-shape : ∀ {i h t} → shape i h (1+ t) → t < hom-size i h
<-from-shape = S≤-<

Shape = Σ[ i ﹕ ℕ ] Σ[ h ﹕ ℕ ] Σ[ t ﹕ ℕ ] shape i h t

𝑖 : Shape → ℕ
𝑖 = fst

ℎ : Shape → ℕ
ℎ = fst ∘ snd

𝑡 : Shape → ℕ
𝑡 = 2nd ∘ snd

is-shape : ((i , h , t , _) : Shape) → shape i h t
is-shape = 3rd ∘ snd

shape-is-prop : ∀ {i h t} → is-prop (shape i h t)
shape-is-prop = ≤-is-prop

shape-path : ∀ {i h t} (s s' : shape i h t) → s == s'
shape-path = prop-has-all-paths

\end{code}


Counting factors
----------------

\begin{code}

discrim : ∀ i h t u → ∀ {j} (f : hom i j) → Dec (f ∣ #[ t ] i h u)
discrim i h t u f = f ∣? #[ t ] i h u

count-factors :
  ∀ i h t
  → shape i h t
  → ∀ {j} → hom i j
  → ℕ
count-factors-aux :
  ∀ i h t
  → (u : t < hom-size i h)
  → ∀ {j} (f : hom i j)
  → Dec (f ∣ (#[ t ] i h u))
  → ℕ

count-factors i h O s f = O
count-factors i h (1+ t) s f =
  let u = <-from-shape s in
  count-factors-aux i h t u f $ discrim i h t u f

count-factors-aux i h t u f (inr no) =
  count-factors i h t (<-to-shape u) f
count-factors-aux i h t u f (inl yes) =
  1+ (count-factors i h t (<-to-shape u) f)

\end{code}

* The following is Lemma 6.22 of the paper (as of 31.01.2024).

\begin{code}

count-factors-top-level : -- 6.22
  ∀ i h t s (f : hom i h) → count-factors i h t s f == O
count-factors-top-level-aux :
  ∀ i h t u f d → count-factors-aux i h t u f d == O

count-factors-top-level i h O s f = idp
count-factors-top-level i h (1+ t) s f =
  let u = <-from-shape s in
  count-factors-top-level-aux i h t u f $ discrim i h t u f

count-factors-top-level-aux i h t u f (inl (g , _)) =
  ⊥-rec (endo-hom-empty g)
count-factors-top-level-aux i h t u f (inr no) =
  count-factors-top-level i h t (<-to-shape u) f

\end{code}

Basic properties of `count-factors`.

\begin{code}

count-factors-divisible-aux :
  ∀ i h t u {j} (f : hom i j) d
  → f ∣ #[ t ] i h u
  → count-factors-aux i h t u f d == 1+ (count-factors i h t (<-to-shape u) f)
count-factors-divisible-aux i h t u f (inl _) yes = idp
count-factors-divisible-aux i h t u f (inr no) yes = ⊥-rec $ no yes

count-factors-divisible :
  ∀ i h t s {j} (f : hom i j)
  → f ∣ #[ t ] i h (<-from-shape s)
  → count-factors i h (1+ t) s f == 1+ (count-factors i h t (prev-shape s) f)
count-factors-divisible i h t s f yes =
  let u = <-from-shape s in
  count-factors-divisible-aux i h t u f (discrim i h t u f) yes

\end{code}

* Proposition 6.24 (31.01.2024)

\begin{code}

module _ -- 6.24
  (i h : ℕ) {j : ℕ} (f : hom i j)
  ((t₀ , u₀) : Fin (hom-size i h))
  (divisible : f ∣ #[ t₀ ] i h u₀)
  (smallest : (∀ t u → f ∣ #[ t ] i h u → t₀ ≤ t))
  where

  count-factors-below-first-divisible :
    ∀ t s → t ≤ t₀ → count-factors i h t s f == O
  count-factors-below-first-divisible-aux :
    ∀ t u d → 1+ t ≤ t₀ → count-factors-aux i h t u f d == O

  count-factors-below-first-divisible O s w = idp
  count-factors-below-first-divisible (1+ t) s w =
    let u = <-from-shape s in
    count-factors-below-first-divisible-aux t u (discrim i h t u f) w

  count-factors-below-first-divisible-aux t u (inl yes) w =
    ⊥-rec $ S≰ $ ≤-trans w $ smallest _ _ yes
  count-factors-below-first-divisible-aux t u (inr no) w =
    count-factors-below-first-divisible t (<-to-shape u) (S≤-≤ w)

\end{code}

* Lemma 6.25 (31.01.2024)

\begin{code}

module _ (i h : ℕ) {j} (f : hom i j) where -- 6.25
  count-factors-all-O-hom-size-O :
    (∀ t s → count-factors i h t s f == O)
    → hom-size j h == O
  count-factors-all-O-hom-size-O all-O = ¬O<-=O (hom-size j h) bot
    where module _ (O<homjh : O < hom-size j h) where
      [O] = #[ O ] j h O<homjh
      t₀ = idx ([O] ◦ f)
      u₀  = idx<hom-size ([O] ◦ f)
      s₀ = <-S≤ u₀

      p : count-factors i h (1+ t₀) s₀ f == 1+ (count-factors i h t₀ _ f)
      p = count-factors-divisible i h t₀ s₀ f (∣◦hom#-idx f [O])

      bot : ⊥
      bot = ℕ-O≠S _ (! (all-O (1+ t₀) s₀) ∙ p)

  hom-size-O-no-divisible :
    hom-size j h == O
    → ∀ t u → ¬ (f ∣ #[ t ] i h u)
  hom-size-O-no-divisible p t u (g , _) =
    ≮O _ $ transp (O <_) p $ hom[ j , h ]-inhab g

  no-divisible-count-factors-all-O :
    (∀ t u → ¬ (f ∣ #[ t ] i h u))
    → ∀ t s → count-factors i h t s f == O
  no-divisible-count-factors-all-O-aux :
    (∀ t u → ¬ (f ∣ #[ t ] i h u))
    → ∀ t u d → count-factors-aux i h t u f d == O

  no-divisible-count-factors-all-O no-div O s = idp
  no-divisible-count-factors-all-O no-div (1+ t) s =
    let u = <-from-shape s in
    no-divisible-count-factors-all-O-aux no-div t u $ discrim i h t u f

  no-divisible-count-factors-all-O-aux no-div t u (inl yes) =
    ⊥-rec $ no-div _ _ yes
  no-divisible-count-factors-all-O-aux no-div t u (inr no) =
    no-divisible-count-factors-all-O no-div t (<-to-shape u)

  -- Lots of annoying finagling to the right form in this.
  -- Could probably do it more concisely.
  hom-size>O-exists-divisible :
    O < hom-size j h
    → Σ (Fin (hom-size i h)) λ (t , u) → f ∣ #[ t ] i h u
  hom-size>O-exists-divisible O<homjh =
    ¬∀Fin¬ _ _ (λ (t , u) → f ∣? #[ t ] i h u)
      $ ¬uncurry $ c $ ≠-inv $ <-to-≠ O<homjh
    where
    no-divisible-hom-size-O =
      count-factors-all-O-hom-size-O ∘ no-divisible-count-factors-all-O
    c = contrapos no-divisible-hom-size-O

\end{code}


Division by morphisms
---------------------

Assume that I is strictly oriented, and that i, h, j : I₀ such that
  | I(j, h) | > 0,
with f : I(i, j). This means that there is a smallest index
  (t₀, u₀) : Fin | I(i, h) |
such that f ∣ [t₀].

\begin{code}

module Cosieves-StrictlyOriented
  (I-strictly-oriented : is-strictly-oriented I)
  where

  open SimpleSemicategories-IsStrictlyOriented I I-strictly-oriented

  module _ (i h j : ℕ) (f : hom i j) (O<homjh : O < hom-size j h) where

    O<homih : O < hom-size i h
    O<homih = hom[ i , h ]-inhab (#[ O ] j h O<homjh ◦ f)

    smallest-divisible :
      Σ (Fin (hom-size i h)) (is-smallest-Fin (λ (t , u) → f ∣ #[ t ] i h u))
    smallest-divisible =
      uncurry (Fin-smallest-witness (λ (t , u) → f ∣? #[ t ] i h u))
        $ hom-size>O-exists-divisible i h f O<homjh

    t₀ = to-ℕ $ fst smallest-divisible
    u₀ = snd $ fst smallest-divisible
    t₀-divisible = 2nd smallest-divisible
    t₀-smallest = curry (3rd smallest-divisible)

\end{code}

Now define division by f.

\begin{code}

    divby : ∀ t → t < hom-size i h → hom j h
    divby-aux : ∀ t (u : t < hom-size i h) → Dec (f ∣ #[ t ] i h u) → hom j h

    divby t u = divby-aux t u $ discrim i h t u f

    divby-aux t u (inl (g , _)) = g
    divby-aux O u (inr no) = #[ O ] j h O<homjh
    divby-aux (1+ t) u (inr no) = divby t (S<-< u)

\end{code}

A few basic observations about `divby`:

\begin{code}

    divby-value-aux :
      ∀ t u d g
      → g ◦ f == #[ t ] i h u
      → divby-aux t u d == g
    divby-value-aux t u (inl (_ , q)) g p = hom-is-epi _ _ _ (q ∙ ! p)
    divby-value-aux t u (inr no) g p = ⊥-rec $ no (g , p)

    divby-value :
      ∀ t u g
      → g ◦ f == #[ t ] i h u
      → divby t u == g
    divby-value t u = divby-value-aux t u (discrim i h t u f)

    divby-divisible-◦-aux :
      ∀ t u d → f ∣ #[ t ] i h u → divby-aux t u d ◦ f == #[ t ] i h u
    divby-divisible-◦-aux t u (inl (_ , p)) yes = p
    divby-divisible-◦-aux t u (inr no) yes = ⊥-rec $ no yes

    divby-divisible-◦ :
      ∀ t u → f ∣ #[ t ] i h u → divby t u ◦ f == #[ t ] i h u
    divby-divisible-◦ t u = divby-divisible-◦-aux t u $ discrim i h t u f

\end{code}

* Lemma 6.26 (31.01.2024)

\begin{code}
    divby-is-lub : -- 6.26
      ∀ t u g
      → g ◦ f ≼ #[ t ] i h u
      → g ≼ divby t u
    divby-is-lub-aux :
      ∀ t u d g
      → g ◦ f ≼ #[ t ] i h u
      → g ≼ divby-aux t u d

    divby-is-lub t u = divby-is-lub-aux t u $ discrim i h t u f

    divby-is-lub-aux O u d g w =
      =-≼ (! (divby-value-aux _ _ d _ (≼[O] _ _ w)))
    divby-is-lub-aux (1+ t) u (inl (g' , p)) g w =
      ≼-cancel-r _ _ _ (transp (_ ≼_) (! p) w)
    divby-is-lub-aux (1+ t) u (inr no) g (inl p) =
      ⊥-rec $ no (g , idx=-hom= p)
    divby-is-lub-aux (1+ t) u (inr no) g (inr w) =
      divby-is-lub t (S<-< u) g (≺#S-≼# _ _ w)

\end{code}

* Lemma 6.27 (01.02.2024)

\begin{code}

    divby-<-smallest-divisible :
      ∀ t u → t < t₀ → divby t u == #[ O ] j h O<homjh
    divby-<-smallest-divisible-aux :
      ∀ t u d → t < t₀ → divby-aux t u d == #[ O ] j h O<homjh

    divby-<-smallest-divisible t u =
      divby-<-smallest-divisible-aux t u $ discrim i h t u f

    divby-<-smallest-divisible-aux t u (inl yes) v =
      ⊥-rec $ ¬<-self $ <-≤-< v (t₀-smallest _ _ yes)
    divby-<-smallest-divisible-aux O u (inr no) v = idp
    divby-<-smallest-divisible-aux (1+ t) u (inr no) v =
      divby-<-smallest-divisible t (S<-< u) (S<-< v)

    divby-smallest-divisible : divby t₀ u₀ == #[ O ] j h O<homjh
    divby-smallest-divisible = ≼[O] O<homjh _ (≼-cancel-r _ _ _ w')
      where
      [O]◦f = #[ O ] j h O<homjh ◦ f
      [t₀] = #[ t₀ ] i h u₀

      i₀ = idx [O]◦f
      v₀ = idx<hom-size [O]◦f

      p : divby t₀ u₀ ◦ f == [t₀]
      p = divby-divisible-◦ t₀ u₀ t₀-divisible

      -- Wouldn't need all this idx/hom# wrangling with
      -- a more definitional representation of arrows.
      w : [t₀] ≼ [O]◦f
      w = t₀-smallest i₀ v₀ (∣◦hom#-idx f _) ◂$ transp! (_≤ i₀) (idx-hom# _)

      w' : divby t₀ u₀ ◦ f ≼ [O]◦f
      w' = ≼-trans (=-≼ p) w

    divby-◦-ub :
      ∀ t u → t₀ ≤ t → divby t u ◦ f ≼ #[ t ] i h u
    divby-◦-ub-aux :
      ∀ t u d → t₀ ≤ t → divby-aux t u d ◦ f ≼ #[ t ] i h u

    divby-◦-ub t u = divby-◦-ub-aux t u $ discrim i h t u f

    divby-◦-ub-aux t u d (inl idp) =
      =-≼ (divby-divisible-◦-aux t u d (∣#[]= t₀-divisible))
    divby-◦-ub-aux t u (inl yes) (inr v) = =-≼ (snd yes)
    divby-◦-ub-aux (1+ t) u (inr no) (inr v) =
      ≼-≺-≼ (divby-◦-ub t w  (<S-≤ v)) (#[ t ]≺S w u)
      where w = S<-< u

\end{code}

* Lemma 6.28 (01.02.2024)

Morphism division is monotone.

\begin{code}

    divby-<-monotone :
      ∀ {t t'} {u u'}
      → t < t' → divby t u ≼ divby t' u'
    divby-<-monotone {t} .{1+ t} {u} {u'} ltS =
      case (ℕ-trichotomy' t₀ t) case[t₀≤t] case[t<t₀]
      where
      case[t₀≤t] = λ t₀≤t →
        divby-is-lub (1+ t) _ _ $ ≼-≺-≼ (divby-◦-ub t _ t₀≤t) (#[ t ]≺S _ _)
      case[t<t₀] = λ t<t₀ →
        [O]-min _ _
          ◂$ transp! (_≼ _) (divby-<-smallest-divisible _ _ t<t₀)
    divby-<-monotone {t} {1+ t'} {u} {u'} (ltSR w) =
      ≼-trans
        (divby-<-monotone {t} {t'} {u} {S<-< u'} w)
        (divby-<-monotone {t'} {1+ t'} ltS)

    divby-≤-monotone :
      ∀ {t t'} {u u'}
      → t ≤ t' → divby t u ≼ divby t' u'
    divby-≤-monotone (inl idp) = =-≼ (ap (divby _) (<-has-all-paths _ _))
    divby-≤-monotone (inr w) = divby-<-monotone w

    divby-reflects-<-monotone :
      ∀ {t t'} {u u'}
      → divby t u ≺ divby t' u'
      → t < t'
    divby-reflects-<-monotone w = ≰-to-> λ c → ≤-to-≯ (divby-≤-monotone c) w

\end{code}

* Proposition 6.29 (01.02.2024)

Morphism division is surjective.

\begin{code}

    divby-surj : (g : hom j h) → divby (idx (g ◦ f)) (idx<hom-size (g ◦ f)) == g
    divby-surj g =
      divby-value (idx (g ◦ f)) (idx<hom-size (g ◦ f)) g (! (hom#-idx _))

\end{code}

* Corollary 6.30 (01.02.2024)

Upper bound on idx([t+1]/f).

\begin{code}

    idx-divby-S-upper-bound :
      (t : ℕ) (u : 1+ t < hom-size i h)
      → idx (divby (1+ t) u) ≤ 1+ (idx (divby t (S<-< u)))
    idx-divby-S-upper-bound t u =
      case (<-S≤ m<homjh) case[m+1=homjh] case[m+1<homjh]
      where
      [t]/f = divby t (S<-< u)
      m = idx [t]/f
      m<homjh = idx<hom-size [t]/f

      [t+1]/f = divby (1+ t) u
      n = idx [t+1]/f
      n<homjh = idx<hom-size [t+1]/f

      case[m+1=homjh] = λ m+1=homjh → inr (transp! (n <_) m+1=homjh n<homjh)

      case[m+1<homjh] = λ m+1<homjh → ≮-to-≥ (bot m+1<homjh)
        where module _ (b : 1+ m < hom-size j h) (c : 1+ m < n) where
        t' = idx (#[ 1+ m ] j h b ◦ f)
        u' = idx<hom-size (#[ 1+ m ] j h b ◦ f)

        p : #[ 1+ m ] j h b == divby t' u'
        p = ! (divby-surj _)

        v : [t]/f ≺ divby t' u'
        v = #[ m ]≺S m<homjh b
               ◂$ transp (_≺ #[ 1+ m ] j h b) (hom#-idx _)
               ◂$ transp ([t]/f ≺_) p

        v' : divby t' u' ≺ [t+1]/f
        v' = transp (_< _) (! (idx-hom# _) ∙ ap idx p) c

        w : t < t'
        w = divby-reflects-<-monotone v

        w' : t' < 1+ t
        w' = divby-reflects-<-monotone v'

        bot : ⊥
        bot = no-between w w'

\end{code}

    divby-1+≼-divby-to-= :
      ∀ {t} {u} {v}
      → divby (1+ t) u ≼ divby t v
      → divby (1+ t) u == divby t v
    divby-1+≼-divby-to-= (inl p) = idx=-hom= p
    divby-1+≼-divby-to-= (inr w) = ⊥-rec $ S≮ $ divby-reflects-monotone _ _ w

    idx-divby-1+-divisible :
      (t : ℕ) (u : 1+ t < hom-size i h)
      → t₀ ≤ t
      → f ∣ #[ 1+ t ] i h u
      → idx (divby (1+ t) u) == 1+ (idx (divby t (S<-< u)))
    idx-divby-1+-divisible t u v d with f ∣? #[ 1+ t ] i h u
    ... | inr no = ⊥-rec $ no d
    ... | inl (g , p)
          with idx-divby-1+-upper-bound t u
    ...   | inl q = (ap idx $ ! (divby-value p)) ∙ q
    ...   | inr w = ⊥-rec $ S≰ contra
            where
            r : divby (1+ t) u == divby t (S<-< u)
            r = divby-1+≼-divby-to-= (<S-≤ w)

            c : #[ 1+ t ] i h u ≼ #[ t ] i h (S<-< u)
            c = divby-◦-ub t _ v
                ◂$ transp! (λ ◻ → ◻ ◦ f ≼ #[ t ] i h _) r
                ◂$ transp (_≼ #[ t ] i h (S<-< u)) (divby-divisible-◦ _ _ d)

            contra : 1+ t ≤ t
            contra = c ◂$ transp (idx (#[ 1+ t ] i h _) ≤_) (idx-hom# t)
                       ◂$ transp (_≤ t) (idx-hom# (1+ t))

    -- 6.32
    abstract
      count-factors-idx-divby :
        (t : ℕ) (u : t < hom-size i h) (s : shape i h (1+ t))
        → t₀ ≤ t
        → count-factors i h (1+ t) s f == 1+ (idx (divby t u))
      count-factors-idx-divby t u s (inl idp) = p ∙ ap 1+ (q ∙ ! r)
        where
        p : count-factors i h (1+ t₀) s f
            == 1+ (count-factors i h t₀ (prev-shape s) f)
        p = count-factors-divisible t₀ s (∣#[]= t₀-divisible)

        q : count-factors i h t₀ (prev-shape s) f == O
        q = count-factors-O-below-first-divisible t₀ lteE

        r : idx (divby t₀ u) == O
        r = hom=-idx= (ap (divby t₀) (<-has-all-paths _ _) ∙ divby-smallest-divisible)
            ∙ idx-hom# _
      count-factors-idx-divby (1+ t) u s (inr w)
       with count-factors-discrim i h (1+ t) (S≤-< s) f
          | divby-discrim (1+ t) u
      ... | inl yes | inl yes'@(g , p)
            =
            q ∙ ap 1+ (! (idx-divby-1+-divisible t u (<S-≤ w) yes')
                       ∙ ap idx (divby-value p))
            where
            q : count-factors-aux i h (1+ t) (S≤-< s) f (inl yes)
                == 2+ (idx (divby t (S<-< u)))
            q = ap 1+
                  (count-factors-idx-divby t (S<-< u) (prev-shape s) (<S-≤ w))
      ... | inr no | inr no' =
              count-factors-idx-divby t (S<-< u) (prev-shape s) (<S-≤ w)
      ... | inl yes | inr no' = ⊥-rec $ no' (∣#[]= yes)
      ... | inr no | inl yes' = ⊥-rec $ no (∣#[]= yes')

  -- module 6∙33 where -- paper version 26.01.24
  --   -- Deviates slightly from paper proof.
  --   count-factors-shape :
  --     ∀ i h t s {j} (f : hom i j)
  --     → count-factors i h t s f ≤ hom-size j h
  --   count-factors-shape[_,_,1+_] :
  --     ∀ i h t u {j} (f : hom i j) d
  --     → count-factors[ i , h ,1+ t ] u f d ≤ hom-size j h

  --   count-factors-shape i h O s f = O≤ _
  --   count-factors-shape i h (1+ t) s f =
  --     let u = S≤-< s in
  --     count-factors-shape[ i , h ,1+ t ] u f (count-factors-discrim[1+ t ] u f)

  --   count-factors-shape[ i , h ,1+ t ] u f (inl yes) = {!!}
  --   count-factors-shape[ i , h ,1+ t ] u f (inr no) =
  --     count-factors-shape i h t (<-shape u) f

  --   private -- experimental; unused
  --     record Shape-helper (i h t : ℕ) ⦃ s : shape i h t ⦄ : Type₀  where
  --       constructor _,_
  --       field
  --         dt : ℕ
  --         eq : dt == hom-size i h − t

  -- open 6∙33 public

  -- module 6∙23 where -- version 17.01.24
  --   count-factors-full :
  --     ∀ i h s {j} (f : hom i j)
  --     → count-factors i h (hom-size i h) s f == hom-size j h
  --   count-factors-full = {!!}

  -- open 6∙23 public

  -- -- Need this too; prove it on paper:
  -- count-factors-comp :
  --   ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
  --   → ∀ {s'}
  --   → count-factors i h t s (g ◦ f)
  --     == count-factors j h (count-factors i h t s f) s' g
  -- count-factors-comp[_,_,1+_] :
  --   ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
  --   → (d : Dec (g ◦ f ∣ #[ t ] i h u))
  --   → ∀ {s'}
  --   → count-factors[ i , h ,1+ t ] u (g ◦ f) d
  --     == count-factors j h (count-factors[ i , h ,1+ t ] u f {!!}) s' g

  -- count-factors-comp i h O s f g = idp
  -- count-factors-comp i h (1+ t) s f g =
  --   count-factors-comp[ i , h ,1+ t ] u f g (g ◦ f ∣? #[ t ] i h u)
  --   where u = S≤-< s

  -- count-factors-comp[ i , h ,1+ t ] u f g (inl yes) = {!!}
  -- count-factors-comp[ i , h ,1+ t ] u f g (inr no) = {!!}
