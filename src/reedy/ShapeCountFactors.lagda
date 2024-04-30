Counting factors of linear cosieves
===================================

Restriction of linear cosieves is implemented via "counting factors".

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.ShapeCountFactors {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open import reedy.CosieveShapes I
open import reedy.ShapeOrder I

open SimpleSemicategory I

\end{code}

The basic definition.

\begin{code}

discrim : ∀ i h t u → ∀ {j} (f : hom i j) → Dec (f ∣ #[ t ] i h u)
discrim i h t u f = f ∣? #[ t ] i h u

count-factors :
  ∀ i h t
  → is-shape i h t
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
  let u = <-from-is-shape s in
  count-factors-aux i h t u f $ discrim i h t u f

count-factors-aux i h t u f (inr no) =
  count-factors i h t (<-to-is-shape u) f
count-factors-aux i h t u f (inl yes) =
  1+ (count-factors i h t (<-to-is-shape u) f)

\end{code}

Equality.

\begin{code}

count-factors= :
  ∀ i h {j} (f : hom i j) t {s} t' {s'}
  → t == t'
  → count-factors i h t s f == count-factors i h t' s' f
count-factors= i h f t t' idp =
  ap (λ ◻ → count-factors i h t ◻ f) (is-shape-path _ _)

\end{code}

Reflect the computation rules because we need them later.

\begin{code}

count-factors-divisible-aux :
  ∀ i h t u {j} (f : hom i j) d
  → f ∣ #[ t ] i h u
  → ∀ {s}
  → count-factors-aux i h t u f d == 1+ (count-factors i h t s f)
count-factors-divisible-aux i h t u f (inl _) yes =
  ap (λ ◻ → 1+ (count-factors i h t ◻ f)) (is-shape-path _ _)
count-factors-divisible-aux i h t u f (inr no) yes =
  ⊥-rec $ no yes

count-factors-divisible :
  ∀ i h t s {j} (f : hom i j)
  → f ∣ #[ t ] i h (<-from-is-shape s)
  → ∀ {s'}
  → count-factors i h (1+ t) s f == 1+ (count-factors i h t s' f)
count-factors-divisible i h t s f yes =
  let u = <-from-is-shape s in
  count-factors-divisible-aux i h t u f (discrim i h t u f) yes

count-factors-not-divisible-aux :
  ∀ i h t u {j} (f : hom i j) d
  → ¬ (f ∣ #[ t ] i h u)
  → ∀ {s}
  → count-factors-aux i h t u f d == count-factors i h t s f
count-factors-not-divisible-aux i h t u f (inl yes) no =
  ⊥-rec $ no yes
count-factors-not-divisible-aux i h t u f (inr _) no =
  ap (λ ◻ → count-factors i h t ◻ f) (is-shape-path _ _)

count-factors-not-divisible :
  ∀ i h t s {j} (f : hom i j)
  → ¬ (f ∣ #[ t ] i h (<-from-is-shape s))
  → ∀ {s'}
  → count-factors i h (1+ t) s f == count-factors i h t s' f
count-factors-not-divisible i h t s f no =
  let u = <-from-is-shape s in
  count-factors-not-divisible-aux i h t u f (discrim i h t u f) no

\end{code}

* The following is Lemma 6.22 of the paper (as of 31.01.2024).

\begin{code}

count-factors-top-level :
  ∀ i h t s (f : hom i h) → count-factors i h t s f == O
count-factors-top-level-aux :
  ∀ i h t u f d → count-factors-aux i h t u f d == O

count-factors-top-level i h O s f = idp
count-factors-top-level i h (1+ t) s f =
  let u = <-from-is-shape s in
  count-factors-top-level-aux i h t u f $ discrim i h t u f

count-factors-top-level-aux i h t u f (inl (g , _)) =
  ⊥-rec (endo-hom-empty g)
count-factors-top-level-aux i h t u f (inr no) =
  count-factors-top-level i h t (<-to-is-shape u) f

\end{code}

* Proposition 6.24 (31.01.2024)

\begin{code}

module _
  (i h : ℕ) {j : ℕ} (f : hom i j)
  (t₀ : ℕ) (u₀ : t₀ < hom-size i h)
  (divisible : f ∣ #[ t₀ ] i h u₀)
  (smallest : (∀ t u → f ∣ #[ t ] i h u → t₀ ≤ t))
  where

  count-factors-below-first-divisible :
    ∀ t s → t ≤ t₀ → count-factors i h t s f == O
  count-factors-below-first-divisible-aux :
    ∀ t u d → 1+ t ≤ t₀ → count-factors-aux i h t u f d == O

  count-factors-below-first-divisible O s w = idp
  count-factors-below-first-divisible (1+ t) s w =
    let u = <-from-is-shape s in
    count-factors-below-first-divisible-aux t u (discrim i h t u f) w

  count-factors-below-first-divisible-aux t u (inl yes) w =
    ⊥-rec $ S≰ $ ≤-trans w $ smallest _ _ yes
  count-factors-below-first-divisible-aux t u (inr no) w =
    count-factors-below-first-divisible t (<-to-is-shape u) (S≤-≤ w)

\end{code}

* Lemma 6.25 (31.01.2024)

\begin{code}

module _ (i h : ℕ) {j} (f : hom i j) where
  count-factors-all-O-hom-size-O :
    (∀ t s → count-factors i h t s f == O)
    → hom-size j h == O
  count-factors-all-O-hom-size-O all-O = ¬O<-=O (hom-size j h) bot
    where module _ (O<homjh : O < hom-size j h) where
      [O] = #[ O ] j h O<homjh
      t₀ = idx ([O] ◦ f)
      u₀  = idx<hom-size ([O] ◦ f)
      s₀ = <-S≤ u₀

      p : count-factors i h (1+ t₀) s₀ f ==
          1+ (count-factors i h t₀ (prev-shape s₀) f)
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
    let u = <-from-is-shape s in
    no-divisible-count-factors-all-O-aux no-div t u $ discrim i h t u f

  no-divisible-count-factors-all-O-aux no-div t u (inl yes) =
    ⊥-rec $ no-div _ _ yes
  no-divisible-count-factors-all-O-aux no-div t u (inr no) =
    no-divisible-count-factors-all-O no-div t (<-to-is-shape u)

  hom-size-O-count-factors-all-O :
    hom-size j h == O
    → ∀ t s → count-factors i h t s f == O
  hom-size-O-count-factors-all-O =
    no-divisible-count-factors-all-O ∘ hom-size-O-no-divisible

  exists-divisible-hom-size>O :
    ∀ t u
    → f ∣ #[ t ] i h u
    → O < hom-size j h
  exists-divisible-hom-size>O t u yes =
    ¬=O-O< _ (λ p → hom-size-O-no-divisible p t u yes)

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

module ShapeCountFactors-StrictlyOriented
  (I-strictly-oriented : is-strictly-oriented I)
  where

  open SimpleSemicategories-IsStrictlyOriented I I-strictly-oriented

  module _ (i h : ℕ) {j : ℕ} (f : hom i j) (O<homjh : O < hom-size j h) where

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
    divby-is-lub :
      ∀ t u g
      → g ◦ f ≼ #[ t ] i h u
      → g ≼ divby t u
    divby-is-lub-aux :
      ∀ t u d g
      → g ◦ f ≼ #[ t ] i h u
      → g ≼ divby-aux t u d

    divby-is-lub t u = divby-is-lub-aux t u $ discrim i h t u f

    divby-is-lub-aux O u d g w =
      =-≼ (! (divby-value-aux _ _ d _ (≼[O]-=[O] _ _ w)))
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

    divby-smallest-divisible-aux :
      ∀ u d → divby-aux t₀ u d == #[ O ] j h O<homjh
    divby-smallest-divisible-aux u (inr no) = ⊥-rec $ no (∣#[]= t₀-divisible)
    divby-smallest-divisible-aux u (inl (g , p)) =
      ≼[O]-=[O] O<homjh _ (≼-cancel-r _ _ _ w')
      where
      [O]◦f = #[ O ] j h O<homjh ◦ f
      i₀ = idx [O]◦f
      v₀ = idx<hom-size [O]◦f

      -- Wouldn't need all this idx/hom# wrangling with a more definitional
      -- representation of arrows.
      w : #[ t₀ ] i h u ≼ [O]◦f
      w = t₀-smallest i₀ v₀ (∣◦hom#-idx f _) ◂$ transp! (_≤ i₀) (idx-hom# _)

      w' : g ◦ f ≼ [O]◦f
      w' = w ◂$ transp! (_≼ [O]◦f) p

    divby-smallest-divisible : ∀ u → divby t₀ u == #[ O ] j h O<homjh
    divby-smallest-divisible u = divby-smallest-divisible-aux u yes
      where
      yes = inl (divby-aux t₀ u (discrim i h t₀ u f)
                , divby-divisible-◦ t₀ u (∣#[]= t₀-divisible))
      -- (discrim i h t₀ u f) in place of (yes) also works, but is less specific.

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
      case (ℕ-trich t₀ t) case[t₀≤t] case[t<t₀]
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

Upper bound on idx([t+1]/f). The upper bound is sharp when f divides [t+1] for
large enough t.

\begin{code}

    idx-divby-S-ub :
      (t : ℕ) (u : 1+ t < hom-size i h)
      → idx (divby (1+ t) u) ≤ 1+ (idx (divby t (S<-< u)))
    idx-divby-S-ub t u =
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

    divby-S-≼-divby-equal :
      ∀ {t} {u} {v}
      → divby (1+ t) u ≼ divby t v
      → divby (1+ t) u == divby t v
    divby-S-≼-divby-equal (inl p) = idx=-hom= p
    divby-S-≼-divby-equal (inr w) = ⊥-rec $ S≮ $ divby-reflects-<-monotone w

    idx-divby-S-divisible :
      (t : ℕ) (u : 1+ t < hom-size i h)
      → t₀ ≤ t
      → f ∣ #[ 1+ t ] i h u
      → idx (divby (1+ t) u) == 1+ (idx (divby t (S<-< u)))
    idx-divby-S-divisible t u v yes =
      case (idx-divby-S-ub t u) case[n=m+1] case[n<m+1]
      where
      [t]/f = divby t (S<-< u)
      m = idx [t]/f

      [t+1]/f = divby (1+ t) u
      n = idx [t+1]/f

      case[n=m+1] = λ p → p
      case[n<m+1] = ⊥-rec ∘ S≰ ∘ d
        where module _ (w : n < 1+ m) where
        p : divby t (S<-< u) ◦ f == #[ 1+ t ] i h u
        p = (! $ ap (_◦ f) (divby-S-≼-divby-equal (<S-≤ w)))
            ∙ divby-divisible-◦ (1+ t) u yes

        c : #[ 1+ t ] i h u ≼ #[ t ] i h (S<-< u)
        c = divby-◦-ub t (S<-< u) v ◂$ transp (_≼ #[ t ] i h (S<-< u)) p

        d : 1+ t ≤ t
        d = #≼#-idx≤ c

\end{code}

* Corollary 6.31

\begin{code}

    idx-divby-max :
      ∀ T J {u : T < hom-size i h} {v : J < hom-size j h}
      → hom-size i h == 1+ T
      → hom-size j h == 1+ J
      → idx (divby T u) == J
    idx-divby-max T J {u} {v} p q = ≤-between-= ub lb
      where
      [T]/f = divby T u
      [J] = #[ J ] j h v
      [J]◦f = [J] ◦ f

      ub : idx [T]/f ≤ J
      ub = <S-≤ $ transp (idx [T]/f <_) q $ idx<hom-size [T]/f

      w : idx ([J] ◦ f) ≤ T
      w = <S-≤ $ transp (idx [J]◦f <_) p $ idx<hom-size [J]◦f

      lb : J ≤ idx [T]/f
      lb = divby-≤-monotone w
           ◂$ transp (_≼ [T]/f) (divby-surj [J])
           ◂$ transp (_≤ idx [T]/f) (idx-hom# _)

\end{code}

* Lemma 6.32 (04.02.2024)

The Agda proof differs from the paper: we're still in the module context where
we assume O < hom-size j h and derive the existence of t₀, as opposed to the
paper version where we assume t₀ and get the inequality.

\begin{code}

    count-factors-idx-divby :
      (t : ℕ) (s : is-shape i h (1+ t))
      → t₀ ≤ t
      → count-factors i h (1+ t) s f == 1+ (idx $ divby t (<-from-is-shape s))

    count-factors-idx-divby-aux :
      ∀ t u d
      → t₀ ≤ t
      → count-factors-aux i h t u f d == 1+ (idx $ (divby-aux t u d))

    count-factors-idx-divby t s =
      let u = <-from-is-shape s in
      count-factors-idx-divby-aux t u $ discrim i h t u f

    count-factors-idx-divby-aux t u d (inl idp) =
      p ∙ ap 1+ (! q)
      where
      cf-t₀ = count-factors-below-first-divisible
                i h f t₀ u₀ t₀-divisible t₀-smallest

      p : count-factors-aux i h t₀ u f d == 1
      p = count-factors-divisible-aux i h t₀ u f d (∣#[]= t₀-divisible)
          ∙ (ap 1+ $ cf-t₀ t₀ (<-to-is-shape u) lteE)

      q : idx (divby-aux t₀ u d) == O
      q = ap idx (divby-smallest-divisible-aux u d) ∙ idx-hom# O
    count-factors-idx-divby-aux (1+ t) u (inl yes@(g , p)) (inr w) =
      ap 1+ (count-factors-idx-divby t (<-to-is-shape u) (<S-≤ w) ∙ q)
      where
      q : 1+ (idx $ divby t (S<-< u)) == idx g
      q = ! (idx-divby-S-divisible t u (<S-≤ w) yes)
          ∙ ap idx (divby-value (1+ t) u g p)
    count-factors-idx-divby-aux (1+ t) u (inr no) (inr w) =
      count-factors-idx-divby t (<-to-is-shape u) (<S-≤ w)

\end{code}

* Corollary 6.33 (12.02.2024)

Proof differs slightly from the paper version, for diagram construction
typechecking reasons.

\begin{code}

  count-factors-is-shape :
    ∀ i h t s {j} (f : hom i j)
    → count-factors i h t s f ≤ hom-size j h
  count-factors-is-shape-aux :
    ∀ i h t u {j} (f : hom i j) d
    → count-factors-aux i h t u f d ≤ hom-size j h

  count-factors-is-shape i h O s f = O≤ _
  count-factors-is-shape i h (1+ t) s f =
    let u = <-from-is-shape s in
    count-factors-is-shape-aux i h t u f $ discrim i h t u f

  count-factors-is-shape-aux i h t u {j} f d@(inl yes@(g , _)) =
    case (O≤ $ hom-size j h) case[O=homjh] case[O<homjh]
    where
    case[O=homjh] = λ p →
      ⊥-rec $ hom-size-O-no-divisible i h f (! p) t u yes
    case[O<homjh] = λ w →
      <-S≤ (idx<hom-size g) ◂$ transp! (_≤ hom-size j h) (p w)
      where module _ (w : O < hom-size j h) where
      p : count-factors-aux i h t u f d == 1+ (idx g)
      p = count-factors-idx-divby-aux i h f w t u d
            $ t₀-smallest _ _ f w _ u yes
  count-factors-is-shape-aux i h t u f (inr no) =
    count-factors-is-shape i h t (<-to-is-shape u) f

\end{code}

* Lemma 6.34 (12.02.2024)

\begin{code}

  count-factors-full :
    ∀ i h s {j} (f : hom i j)
    → count-factors i h (hom-size i h) s f == hom-size j h
  count-factors-full i h s {j} f =
    case (O≤ $ hom-size j h) case[O=homjh] case[O<homjh]
    where
    case[O=homjh] = λ p →
      hom-size-O-count-factors-all-O i h f (! p) _ s ∙ p
    case[O<homjh] = r
      where module _ (u : O < hom-size j h) where
      v : O < hom-size i h
      v = O<homih i h f u

      w : Σ ℕ λ K → 1+ K == hom-size j h
      w = O<-witness u

      w' : Σ ℕ λ T → 1+ T == hom-size i h
      w' = O<-witness v

      K = fst w
      p = snd w
      T = fst w'
      q = snd w'

      s' : is-shape i h (1+ T)
      s' = transp! (is-shape i h) q s

      r : count-factors i h (hom-size i h) s f == hom-size j h
      r =
        count-factors i h (hom-size i h) s f
          =⟨ count-factors= _ _ f _ _ {s' = s'} (! q) ⟩
        count-factors i h (1+ T) s' f
          =⟨ count-factors-idx-divby i h f u T s'
               (<S-≤ (u₀ i h f u ◂$ transp! (t₀ i h f u <_) q)) ⟩
        1+ (idx $ divby i h f u T (S≤-< s'))
          =⟨ ap 1+ $
              idx-divby-max i h f u T K
                {v = transp (K <_) p ltS}
                (! q) (! p) ⟩
        1+ K
          =⟨ p ⟩
        hom-size j h
          =∎

\end{code}

* Lemma 6.35 (12.02.2024)

\begin{code}

  divisible-factor-idx-count-factors :
    ∀ i h t u {j} (f : hom i j)
    → (m : hom j h)
    → m ◦ f == #[ t ] i h u
    → ∀ {s}
    → idx m == count-factors i h t s f
  divisible-factor-idx-count-factors i h t u f m p =
    =-cancel-S $
      ( ! (divby-value _ _ f O<homjh _ _ m p)
        ∙ ap (divby i h f _ t) (<-has-all-paths _ _)
      |in-ctx (1+ ∘ idx) )
      ∙ ! (count-factors-idx-divby i h f O<homjh t v t₀≤t)
      ∙ count-factors-divisible _ _ _ v f (∣#[]= (m , p))
    where
    O<homjh = hom[ _ , _ ]-inhab m
    t₀≤t = t₀-smallest _ _ _ O<homjh _ _ (m , p)
    v = <-S≤ u

  count-factors-<-hom-size :
    ∀ i h t u {j} (f : hom i j)
    → f ∣ #[ t ] i h u
    → ∀ {s}
    → count-factors i h t s f < hom-size j h
  count-factors-<-hom-size i h t u f (m , p) =
    idx<hom-size _
      ◂$ transp (_< _) (divisible-factor-idx-count-factors _ _ _ u f m p)

  divisible-factor-count-factors :
    ∀ i h t u {j} (f : hom i j)
    → (m : hom j h)
    → m ◦ f == #[ t ] i h u
    → ∀ {s} {v}
    → m == #[ count-factors i h t s f ] j h v
  divisible-factor-count-factors i h t u f m p =
    idx=-hom= $
      divisible-factor-idx-count-factors i h t u f m p ∙ ! (idx-hom# _)

\end{code}

* Lemma 6.36 (12.02.2024)

Let i, h : I₀ and f : I(i, j), g : I(j, k). Then (g ◦ f) divides [t]ⁱₕ iff f
divides [t]ⁱₕ and g divides [count-factors i h t f]ʲₕ.

Split this into parts:
1. If g ◦ f ∣ [t]ⁱₕ then f ∣ [t]ⁱₕ.
2. If g ◦ f ∣ [t]ⁱₕ then g ∣ [count-factors...]ʲₕ.
3. If g ◦ f ∤ [t]ⁱₕ and f ∣ [t]ⁱₕ then g ∤ [count-factors i h t f]

\begin{code}

  comp-divides-first-divides :
    ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
    → g ◦ f ∣ #[ t ] i h u
    → f ∣ #[ t ] i h u
  comp-divides-first-divides i h t u f g (m , p) = (m ◦ g) , ass ∙ p

  comp-divides-second-divides :
    ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
    → g ◦ f ∣ #[ t ] i h u
    → ∀ {s} {v}
    → g ∣ #[ count-factors i h t s f ] j h v
  comp-divides-second-divides i h t u f g (m , p) =
    m ,
    (idx=-hom= $
      divisible-factor-idx-count-factors i h t u f (m ◦ g) (ass ∙ p)
      ∙ ! (idx-hom# _))

  both-divide-comp-divides :
    ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
    → f ∣ #[ t ] i h u
    → ∀ {s} {v}
    → g ∣ #[ count-factors i h t s f ] j h v
    → g ◦ f ∣ #[ t ] i h u
  both-divide-comp-divides i h t u {j} f g (m , p) {s} {v} (m' , p') =
    m' , ! ass ∙ ap (_◦ f) (p' ∙ ! q) ∙ p
    where
    q : m == #[ count-factors i h t s f ] j h v
    q = divisible-factor-count-factors _ _ _ _ f m p

  comp-divides-contra :
    ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
    → f ∣ #[ t ] i h u
    → ¬ (g ◦ f ∣ #[ t ] i h u)
    → ∀ {s} {v}
    → ¬ (g ∣ #[ count-factors i h t s f ] j h v)
  comp-divides-contra i h t u f g w c =
    (contrapos $ both-divide-comp-divides i h t u f g w) c

\end{code}

**Lemma**

To be written up in the paper.

\begin{code}

  count-factors-comp :
    ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
    → let cf = count-factors i h t s f in
      (cfs : is-shape j h cf)
    → count-factors i h t s (g ◦ f) ==
      count-factors j h cf cfs g

  count-factors-comp-aux :
    ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
    → (dgf : Dec (g ◦ f ∣ #[ t ] i h u))
    → (df : Dec (f ∣ #[ t ] i h u))
    → let cf = count-factors-aux i h t u f df in
      (cfs : is-shape j h cf)
    → count-factors-aux i h t u (g ◦ f) dgf ==
      count-factors j h cf cfs g

  count-factors-comp i h O s f g _ = idp
  count-factors-comp i h (1+ t) s f g =
    let u = <-from-is-shape s in
    count-factors-comp-aux i h t u f g
      (discrim i h t u (g ◦ f))
      (discrim i h t u f)

  count-factors-comp-aux i h t u {j} f g (inl yes[gf]) df@(inl yes[f]) cfs =
    ap 1+ (count-factors-comp i h t (<-to-is-shape u) f g prev-cfs) ∙ ! p
    where
    cf = count-factors i h t (<-to-is-shape u) f
    prev-cfs = prev-shape cfs

    g∣[r] = comp-divides-second-divides i h t u f g yes[gf]

    p : count-factors j h (1+ cf) cfs g ==
        1+ (count-factors j h cf prev-cfs g)
    p = count-factors-divisible j h cf cfs g g∣[r]

  count-factors-comp-aux i h t u f g (inl yes[gf]) (inr no[f]) cfs =
    ⊥-rec $ no[f] $ comp-divides-first-divides i h t u f g yes[gf]

  count-factors-comp-aux i h t u {j} f g (inr no[gf]) df@(inl yes[f]) cfs =
    count-factors-comp i h t (<-to-is-shape u) f g prev-cfs ∙ ! p
    where
    cf = count-factors i h t (<-to-is-shape u) f
    prev-cfs = prev-shape cfs

    g∤[r] = comp-divides-contra i h t u f g yes[f] no[gf]

    p : count-factors j h (1+ cf) cfs g ==
        count-factors j h cf prev-cfs g
    p = count-factors-not-divisible j h cf cfs g g∤[r]

  count-factors-comp-aux i h t u f g (inr no[gf]) (inr no[f]) =
    count-factors-comp i h t (<-to-is-shape u) f g

\end{code}

The restriction of a linear cosieve of shape (i, h, t) along
  f : hom i j
has shape
  (j, h, count-factors (i, h, t) f).

This operation is decreasing with respect to ≤ₛ.

\begin{code}

restr-≤ₛ-decr :
  (sh@(shape i h t s) : Shape) {j : ℕ} (f : hom i j)
  → let cf = count-factors i h t s f in
    (cfs : is-shape j h cf)
  → shape j h cf cfs ≤ₛ sh
restr-≤ₛ-decr sh f cfs = inr (on-𝑖 (hom-inverse _ _ f))

\end{code}
