{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.Cosieves {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I


{- Shapes of linear cosieves -}

shape : ℕ → ℕ → ℕ → Type₀
shape i h t = t ≤ hom-size i h

prev-shape : ∀ {i h t} → shape i h (1+ t) → shape i h t
prev-shape = S≤-≤

full-shape : ∀ i h → shape i h (hom-size i h)
full-shape i h = lteE

total-shape-1+ : ∀ i → shape (1+ i) i (hom-size (1+ i) i)
total-shape-1+ i = full-shape (1+ i) i

<-shape : ∀ {i h t} → t < hom-size i h → shape i h t
<-shape = inr

Shape = Σ[ i ﹕ ℕ ] Σ[ h ﹕ ℕ ] Σ[ t ﹕ ℕ ] shape i h t

𝑖 : Shape → ℕ
𝑖 = fst

ℎ : Shape → ℕ
ℎ = fst ∘ snd

𝑡 : Shape → ℕ
𝑡 = 2nd ∘ snd

is-shape : ((i , h , t , _) : Shape) → shape i h t
is-shape = 3rd ∘ snd


{- Shape equality -}

shape-is-prop : ∀ {i h t} → is-prop (shape i h t)
shape-is-prop = ≤-is-prop

shape-path : ∀ {i h t} (s s' : shape i h t) → s == s'
shape-path = prop-has-all-paths


{- Counting factors -}

count-factors :
  ∀ i h t → shape i h t → ∀ {j} → hom i j → ℕ
count-factors[_,_,1+_] :
  ∀ i h t (u : t < hom-size i h) {j} (f : hom i j)
  → Dec (f ∣ (#[ t ] i h u))
  → ℕ

count-factors-discrim[1+_] :
  ∀ {i h} t u {j} (f : hom i j) → Dec (f ∣ #[ t ] i h u       )
count-factors-discrim[1+_] {i} {h} t u f = f ∣? #[ t ] i h u

count-factors i h O s f = O
count-factors i h (1+ t) s f =
  let u = S≤-< s in
  count-factors[ i , h ,1+ t ] u f (count-factors-discrim[1+ t ] u f)

count-factors[ i , h ,1+ t ] u f (inr no) =
  count-factors i h t (<-shape u) f
count-factors[ i , h ,1+ t ] u f (inl yes) =
  1+ (count-factors i h t (<-shape u) f)

module 6∙22 where -- paper version as of 16.01.24
  count-factors-top-level :
    ∀ i h t (s : shape i h t) (f : hom i h)
    → count-factors i h t s f == O
  count-factors-top-level i h O s f = idp
  count-factors-top-level i h (1+ t) s f
   with count-factors-discrim[1+ t ] (S≤-< s) f
  ... | inl (g , _) = ⊥-rec (endo-hom-empty g)
  ... | inr no = count-factors-top-level i h t (prev-shape s) f

open 6∙22 public


module count-factors-basic-properties (i h j : ℕ) (f : hom i j) where
  count-factors-div :
    ∀ t s
    → f ∣ #[ t ] i h (S≤-< s)
    → count-factors i h (1+ t) s f == 1+ (count-factors i h t (prev-shape s) f)
  count-factors-div t s f∣[t] with count-factors-discrim[1+ t ] (S≤-< s) f
  ... | inl _ = idp
  ... | inr no = ⊥-rec $ no f∣[t]

  module 6∙25 where -- Proof here differs from the paper
    count-factors-all-O-hom-size-O :
      (∀ t s → count-factors i h t s f == O)
      → hom-size j h == O
    count-factors-all-O-hom-size-O cf-all-O =
      ¬O<-=O (hom-size j h) assuming<O.get-⊥
      where
      module assuming<O (w : O < hom-size j h) where
        [0] = #[ O ] j h w
        idx₀ = idx-of ([0] ◦ f)
        t₀ = fst idx₀
        u  = snd idx₀
        s₀ = <-S≤ u

        f∣[t₀] : f ∣ #[ t₀ ] i h u
        f∣[t₀] rewrite hom#-idx ([0] ◦ f) = [0] , idp

        f∣[t₀]' = f∣[t₀]
          ◂$ transp (λ u → f ∣ #[ t₀ ] i h u) (<-has-all-paths _ _)

        lem : count-factors i h (1+ t₀) s₀ f ≠ O
        lem with count-factors-discrim[1+ t₀ ] (S≤-< s₀) f
        ... | inl yes = ℕ-S≠O _
        ... | inr no = ⊥-rec $ no f∣[t₀]'

        get-⊥ : ⊥
        get-⊥ = lem $ cf-all-O (1+ t₀) s₀

    hom-size-O-no-divisible :
      hom-size j h == O
      → ∀ t u → ¬ (f ∣ #[ t ] i h u)
    hom-size-O-no-divisible p t u (g , _) =
      ≮O _ $ transp (O <_) p $ hom[ j , h ]-inhab g

    no-divisible-count-factors-all-O :
      (∀ t u → ¬ (f ∣ #[ t ] i h u))
      → ∀ t s → count-factors i h t s f == O
    no-divisible-count-factors-all-O no-div O s = idp
    no-divisible-count-factors-all-O no-div (1+ t) s
     with count-factors-discrim[1+ t ] (S≤-< s) f
    ... | inl yes = ⊥-rec $ no-div _ _ yes
    ... | inr no = no-divisible-count-factors-all-O no-div t (prev-shape s)

    -- Lots of annoying finagling to the right form in this...could probably do
    -- all this more concisely.
    hom-size>O-exists-divisible :
      O < hom-size j h
      → Σ (Fin (hom-size i h)) λ (t , u) → f ∣ #[ t ] i h u
    hom-size>O-exists-divisible O<hom =
      ¬∀Fin¬ _ _ (λ (t , u) → f ∣? #[ t ] i h u) $
        ¬uncurry $ contra $ ≠-inv $ <-to-≠ O<hom
      where
      no-divisible-hom-size-O =
        count-factors-all-O-hom-size-O ∘ no-divisible-count-factors-all-O
      contra = contrapos no-divisible-hom-size-O

  open 6∙25 public

  module count-factors-smallest-divisible
    (t₀ : ℕ)
    (u₀ : t₀ < hom-size i h)
    (divisible : f ∣ #[ t₀ ] i h u₀)
    (smallest : ∀ t u
                → f ∣ #[ t ] i h u
                → t₀ ≤ t)
    where
    module 6∙24 where
      count-factors-O-below-first-divisible :
        ∀ t {s} → t ≤ t₀ → count-factors i h t s f == O
      count-factors-O-below-first-divisible O w = idp
      count-factors-O-below-first-divisible (1+ t) {s} w
       with count-factors-discrim[1+ t ] (S≤-< s) f
      ... | inl yes = ⊥-rec $ S≰ (≤-trans w v)
                      where v = smallest _ _ yes :> (t₀ ≤ t)
      ... | inr no = count-factors-O-below-first-divisible t (S≤-≤ w)

    open 6∙24 public

module Cosieves-IsStrictlyOriented
  (I-strictly-oriented : is-strictly-oriented I)
  where
  open SimpleSemicategories-IsStrictlyOriented I I-strictly-oriented

  module divby {i h j : ℕ} (f : hom i j) (size-cond : O < hom-size j h) where
    open count-factors-basic-properties i h j f

    nonempty-ih : O < hom-size i h
    nonempty-ih = hom[ i , h ]-inhab (#[ O ] j h size-cond ◦ f)

    exists-smallest-divisible :
      Σ (Fin (hom-size i h)) (is-smallest-Fin (λ (t , u) → f ∣ #[ t ] i h u))
    exists-smallest-divisible =
      Fin-smallest-witness (λ (t , u) → f ∣? #[ t ] i h u) (fst div) (snd div)
      where div = hom-size>O-exists-divisible size-cond

    t₀ = to-ℕ (fst exists-smallest-divisible)
    u₀ = snd (fst exists-smallest-divisible)
    t₀-divisible = 2nd exists-smallest-divisible
    t₀-smallest = curry (3rd exists-smallest-divisible)

    open count-factors-smallest-divisible t₀ u₀ t₀-divisible t₀-smallest

    divby-aux : ∀ t u → Dec (f ∣ #[ t ] i h u) → hom j h
    divby-aux t u (inl (g , _)) = g
    divby-aux O u (inr no) =
      #[ O ] j h size-cond
    divby-aux (1+ t) u (inr no) =
      divby-aux t v (f ∣? #[ t ] i h v)
      where v = S<-< u

    divby-discrim : ∀ t u → Dec (f ∣ #[ t ] i h u)
    divby-discrim t u = f ∣? #[ t ] i h u

    divby : ∀ t → t < hom-size i h → hom j h
    divby t u = divby-aux t u (divby-discrim t u)

    abstract
      divby-aux= :
        ∀ {t u} d {g}
        → g ◦ f == #[ t ] i h u
        → divby-aux t u d == g
      divby-aux= (inl (_ , q)) p = hom-is-epi _ _ _ (q ∙ ! p)
      divby-aux= (inr no) {g} p = ⊥-rec $ no (g , p)

      divby= :
        ∀ {t u g}
        → g ◦ f == #[ t ] i h u
        → divby t u == g
      divby= {t} {u} = divby-aux= (divby-discrim t u)

      divby-aux-divisible-◦ :
        ∀ t u d → f ∣ #[ t ] i h u → divby-aux t u d ◦ f == #[ t ] i h u
      divby-aux-divisible-◦ t u (inl (_ , p)) f∣[t] = p
      divby-aux-divisible-◦ t u (inr no) f∣[t] = ⊥-rec $ no f∣[t]

      divby-divisible-◦ :
        ∀ t u → f ∣ #[ t ] i h u → divby t u ◦ f == #[ t ] i h u
      divby-divisible-◦ t u = divby-aux-divisible-◦ t u (divby-discrim t u)

    module 6∙26 where
      divby-is-lub-aux :
        ∀ t u d (g : hom j h)
        → g ◦ f ≼ #[ t ] i h u
        → g ≼ divby-aux t u d
      divby-is-lub-aux O u d g w = =-≼ (! (divby-aux= d (≼[O] _ _ w)))
      divby-is-lub-aux (1+ t) u (inl (g' , p)) g w =
        ≼-cancel-r _ _ _ (transp (_ ≼_) (! p) w)
      divby-is-lub-aux (1+ t) u (inr no) g (inl p) =
        ⊥-rec $ no (g , hom= p)
      divby-is-lub-aux (1+ t) u (inr no) g (inr w) =
        divby-is-lub-aux t v d _ (≺S-≼ _ _ w)
        where
        v = S<-< u
        d = f ∣? #[ t ] i h v

      divby-is-lub :
        ∀ t u (g : hom j h)
        → g ◦ f ≼ #[ t ] i h u
        → g ≼ divby t u
      divby-is-lub t u g w = divby-is-lub-aux t u (divby-discrim t u) g w

    open 6∙26 public

    module 6∙27 where
      first-divby : divby t₀ u₀ == #[ O ] j h size-cond
      first-divby = ≼[O] size-cond _ (≼-cancel-r _ _ _ lem)
        where
        [O] = #[ O ] j h size-cond
        [t₀] = #[ t₀ ] i h u₀

        idx₀ = idx-of ([O] ◦ f)
        i₀ = fst idx₀
        v₀ = snd idx₀

        p : divby t₀ u₀ ◦ f == [t₀]
        p = divby-divisible-◦ t₀ u₀ t₀-divisible

        -- Wouldn't need all this index-arrow wrangling with a more
        -- definitional representation of arrows.
        w : [t₀] ≼ [O] ◦ f
        w = idx≤-≼ _ _
          $ transp! (_≤ i₀) (idx-ℕ-hom# _)
          $ t₀-smallest i₀ v₀ (transp! (f ∣_) (hom#-idx ([O] ◦ f)) $ ∣◦ _ _)

        lem : divby t₀ u₀ ◦ f ≼ [O] ◦ f
        lem = ≼-trans (=-≼ p) w

      divby-◦-ub :
        ∀ t u → t₀ ≤ t → divby t u ◦ f ≼ #[ t ] i h u
      divby-◦-ub t u (inl idp) = =-≼ (divby-divisible-◦ t u d)
        where d = transp (f ∣_) #[]-eq t₀-divisible
      divby-◦-ub (1+ t) u (inr v) with divby-discrim (1+ t) u
      ... | inl yes = =-≼ (snd yes)
      ... | inr no = ≼-≺-≼ (divby-◦-ub t w (<S-≤ v)) (#[ t ]≺S w u)
                     where w = S<-< u

    open 6∙27 public

    divby-aux-<-smallest-divisible :
      ∀ t u d → t < t₀ → divby-aux t u d == #[ O ] j h size-cond
    divby-aux-<-smallest-divisible t u (inl yes) w =
      ⊥-rec $ ¬<-self (<-≤-< w (t₀-smallest _ _ yes))
    divby-aux-<-smallest-divisible O u (inr no) w = idp
    divby-aux-<-smallest-divisible (1+ t) u (inr no) w =
      divby-aux-<-smallest-divisible t v (divby-discrim t v) (S<-< w)
      where v = S<-< u

    divby-<-smallest-divisible :
      ∀ t u → t < t₀ → divby t u == #[ O ] j h size-cond
    divby-<-smallest-divisible t u =
      divby-aux-<-smallest-divisible t u (divby-discrim t u)

    module 6∙28 where
      divby-monotone :
        ∀ t {u} t' {u'}
        → t < t'
        → divby t u ≼ divby t' u'
      divby-monotone t .(1+ t) {u'} ltS =
        case (ℕ-trichotomy' t₀ t) case-t₀≤t case-t<t₀
        where
        case-t₀≤t = λ t₀≤t →
          divby-is-lub (1+ t) _ _ $ ≼-≺-≼ (divby-◦-ub t _ t₀≤t) (#[ t ]≺S _ _)

        case-t<t₀ = λ t<t₀ →
          [O]-min _ _
          ◂$ transp! (_≼ _) (divby-<-smallest-divisible _ _ t<t₀)
      divby-monotone t (1+ t') {u'} (ltSR w) =
        ≼-trans
          (divby-monotone t t' {S<-< u'} w)
          (divby-monotone t' (1+ t') ltS)

    open 6∙28

    divby-monotone' :
      ∀ t {u} t' {u'}
      → t ≤ t'
      → divby t u ≼ divby t' u'
    divby-monotone' t t' (inl idp) = =-≼ (ap (divby t) (<-has-all-paths _ _))
    divby-monotone' t t' (inr w) = divby-monotone t t' w

    module 6∙29 where
      divby-surj :
        (g : hom j h)
        → let idx = idx-of (g ◦ f)
        in divby (fst idx) (snd idx) == g
      divby-surj g
       with (let idx = idx-of (g ◦ f) in
            divby-discrim (fst idx) (snd idx))
      ... | inl (g' , p) = hom-is-epi _ _ _ (p ∙ hom#-idx _)
      ... | inr no = ⊥-rec $ no (g , ! (hom#-idx _))

    open 6∙29

    module 6∙31 where
      divby-no-gaps :
        ∀ t (u : 1+ t < hom-size i h) (g : hom j h)
        → divby t (S<-< u) ≼ g
        → g ≺ divby (1+ t) u
        → divby t (S<-< u) == g
      divby-no-gaps t u g w w' = {!divby-monotone t t'!}
        where
        idx = idx-of (g ◦ f)
        t' = to-ℕ idx
        v = snd idx

        p : g == divby t' v
        p = ! (divby-surj g)

    open 6∙31

    module 6∙32 where
      

    module 6∙33 where
      abstract
        count-factors-idx-divby :
          (t : ℕ) (u : t < hom-size i h) (s : shape i h (1+ t))
          → t₀ ≤ t
          → count-factors i h (1+ t) s f == 1+ (ℕ-idx-of (divby t u))

        count-factors-idx-divby t u s (inl idp) = p ∙ ap 1+ (q ∙ ! r)
          where
          p : count-factors i h (1+ t₀) s f
              == 1+ (count-factors i h t₀ (prev-shape s) f)
          p = count-factors-div t₀ s (∣-transp-<-witness t₀-divisible)

          q : count-factors i h t₀ (prev-shape s) f == O
          q = count-factors-O-below-first-divisible t₀ lteE

          r : ℕ-idx-of (divby t₀ u) == O
          r = ℕ-idx= (ap (divby t) (<-has-all-paths _ _) ∙ first-divby)
              ∙ (ap to-ℕ $ idx-hom# _)

        count-factors-idx-divby (1+ t) u s (inr w)
         with count-factors-discrim[1+ 1+ t ] (S≤-< s) f
            | divby-discrim (1+ t) u
        ... | inl yes | inl yes' = p ∙ {!!}
              where
              p : count-factors[ i , h ,1+ 1+ t ] (S≤-< s) f (inl yes)
                  == 2+ (ℕ-idx-of (divby t (S<-< u)))
              p = ap 1+
                    (count-factors-idx-divby t (S<-< u) (prev-shape s) (<S-≤ w))
        ... | inr no | inr no' =
                count-factors-idx-divby t (S<-< u) (prev-shape s) (<S-≤ w)
        ... | inl yes | inr no' = ⊥-rec $ no' (∣-transp-<-witness yes)
        ... | inr no | inl yes' = ⊥-rec $ no (∣-transp-<-witness yes')

  module 6∙34 where -- paper version 17.10.24
    -- Deviates slightly from paper proof.
    count-factors-shape :
      ∀ i h t s {j} (f : hom i j)
      → count-factors i h t s f ≤ hom-size j h
    count-factors-shape[_,_,1+_] :
      ∀ i h t u {j} (f : hom i j) d
      → count-factors[ i , h ,1+ t ] u f d ≤ hom-size j h

    count-factors-shape i h O s f = O≤ _
    count-factors-shape i h (1+ t) s f =
      let u = S≤-< s in
      count-factors-shape[ i , h ,1+ t ] u f (count-factors-discrim[1+ t ] u f)

    count-factors-shape[ i , h ,1+ t ] u f (inl yes) = {!!}
    count-factors-shape[ i , h ,1+ t ] u f (inr no) =
      count-factors-shape i h t (<-shape u) f

    private -- experimental; unused
      record Shape-helper (i h t : ℕ) ⦃ s : shape i h t ⦄ : Type₀  where
        constructor _,_
        field
          dt : ℕ
          eq : dt == hom-size i h − t

  open 6∙34 public

  module 6∙23 where -- version 17.10.24
    count-factors-full :
      ∀ i h s {j} (f : hom i j)
      → count-factors i h (hom-size i h) s f == hom-size j h
    count-factors-full = {!!}

  open 6∙23 public

  -- Need this too; prove it on paper:
  count-factors-comp :
    ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
    → ∀ {s'}
    → count-factors i h t s (g ◦ f)
      == count-factors j h (count-factors i h t s f) s' g
  count-factors-comp[_,_,1+_] :
    ∀ i h t u {j} (f : hom i j) {k} (g : hom j k)
    → (d : Dec (g ◦ f ∣ #[ t ] i h u))
    → ∀ {s'}
    → count-factors[ i , h ,1+ t ] u (g ◦ f) d
      == count-factors j h (count-factors[ i , h ,1+ t ] u f {!!}) s' g

  count-factors-comp i h O s f g = idp
  count-factors-comp i h (1+ t) s f g =
    count-factors-comp[ i , h ,1+ t ] u f g (g ◦ f ∣? #[ t ] i h u)
    where u = S≤-< s

  count-factors-comp[ i , h ,1+ t ] u f g (inl yes) = {!!}
  count-factors-comp[ i , h ,1+ t ] u f g (inr no) = {!!}
