{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.Cosieves {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I

shape : ℕ → ℕ → ℕ → Type₀
shape i h t = t ≤ hom-size i h

prev-shape : ∀ {i h t} → shape i h (1+ t) → shape i h t
prev-shape = S≤-≤

full-shape : ∀ i h → shape i h (hom-size i h)
full-shape i h = lteE

total-shape-1+ : ∀ i → shape (1+ i) i (hom-size (1+ i) i)
total-shape-1+ i = full-shape (1+ i) i

count-factors : ∀ i h t {j} → shape i h t → hom i j → ℕ
count-factors i h O s f = O
count-factors i h (1+ t) s f =
  if f ∣ #[ t ] i h (S≤-< s)
  then (λ _ → 1+ rec)
  else λ _ → rec
  where rec = count-factors i h t (prev-shape s) f

count-factors-eq : ∀ i h t {j} (f : hom i j) (u u' : shape i h t)
  → count-factors i h t u f == count-factors i h t u' f
count-factors-eq i h t f u u' =
  ap (λ v → count-factors i h t v f) (≤-has-all-paths _ _)

count-factors-rec : ∀ i h t {j} (f : hom i j) (u : shape i h (1+ t))
  → ∀ {v} → f divides #[ t ] i h v
  → count-factors i h (1+ t) u f == 1+ (count-factors i h t (prev-shape u) f)
count-factors-rec i h t f u div with f ∣ #[ t ] i h (S≤-< u)
... | inl yes = ap 1+ (count-factors-eq i h t f _ _)
... | inr no = ⊥-rec $ no (transp (f divides_) (#[]-eq t i h _ _) div)

-- Lemma 6.7 (paper version as of 12.10.23)
count-factors-top-level : ∀ i h t (s : shape i h t) (f : hom i h)
  → count-factors i h t s f == 0
count-factors-top-level i h O s f = idp
count-factors-top-level i h (1+ t) s f with f ∣ #[ t ] i h (S≤-< s)
... | inl yes = ⊥-rec $ ¬divides-same-target i h t (S≤-< s) f yes
... | inr no = count-factors-top-level i h t _ f

-- Lemma 6.10 (12.10.23)
-- The proof here differs from the paper.
module count-factors-properties (i h j : ℕ) (f : hom i j) where
  count-factors-all-O-hom-size-O :
    (∀ t s → count-factors i h t s f == O) → hom-size j h == O
  count-factors-all-O-hom-size-O P =
    ¬O<-=O (hom-size j h) (λ O<homjh →
      O<¬=O (c {O<homjh}) (transp! (O <_) (p) (O<S _)) (P (1+ t₀) w))
    where module _ {u : O < hom-size j h} where
      [0] = #[ O ] j h u
      idx₀ = idx-of ([0] ◦ f)
      t₀ = fst idx₀
      v = snd idx₀
      w = <-S≤ v
      c = count-factors i h (1+ t₀) w f

      f∣[t₀] : f divides #[ t₀ ] i h v
      f∣[t₀] rewrite hom#-idx ([0] ◦ f) = [0] , idp

      p : c == 1+ _
      p = count-factors-rec i h t₀ f (<-S≤ v) f∣[t₀]

  hom-size-O-no-divisible :
    hom-size j h == O → ∀ t u → ¬ (f divides #[ t ] i h u)
  hom-size-O-no-divisible p t u (g , q) =
    ≮O _ $ transp (O <_) p $ hom[ j , h ]-inhab g

  no-divisible-count-factors-all-O :
    (∀ t u → ¬ (f divides #[ t ] i h u)) → ∀ t s → count-factors i h t s f == O
  no-divisible-count-factors-all-O P O s = idp
  no-divisible-count-factors-all-O P (1+ t) s with f ∣ #[ t ] i h (S≤-< s)
  ... | inl yes = ⊥-rec $ P _ _ yes
  ... | inr no = no-divisible-count-factors-all-O P t (S≤-≤ s)

  no-divisible-hom-size-O :
    (∀ t u → ¬ (f divides #[ t ] i h u)) → hom-size j h == O
  no-divisible-hom-size-O =
    count-factors-all-O-hom-size-O ∘ no-divisible-count-factors-all-O

  -- Lots of annoying finagling to the right form in this... could probably do
  -- all this more concisely. Maybe by formulating using ℕ instead of Fin (see
  -- e.g.  Martín's TypeTopology).
  hom-size>O-exists-divisible :
    O < hom-size j h
    → Σ (Fin (hom-size i h)) λ (t , u) → f divides #[ t ] i h u
  hom-size>O-exists-divisible O<hom =
    ¬∀Fin¬ _ _ (λ (t , u) → f ∣ #[ t ] i h u) $
      ¬uncurry $ contra $ ≠-inv $ <-to-≠ O<hom
    where
    contra : hom-size j h ≠ O → ¬ (∀ t u → ¬ (f divides #[ t ] i h u))
    contra = contrapos no-divisible-hom-size-O

module Cosieves-IsStrictlyOriented
  (I-strictly-oriented : is-strictly-oriented I)
  where
  open SimpleSemicategories-IsStrictlyOriented I I-strictly-oriented

  module _ {i j h : ℕ} {size-cond : 0 < hom-size j h} (f : hom i j) where
    0<homih : 0 < hom-size i h
    0<homih = hom[ i , h ]-inhab $ #[ 0 ] j h size-cond ◦ f

    divby : (t : ℕ) → t < hom-size i h → hom j h
    divby O u = if f ∣ #[ 0 ] i h u
      then fst
      else λ _ → #[ 0 ] j h size-cond
    divby (1+ t) u = if f ∣ #[ 1+ t ] i h u
      then fst
      else λ _ → divby t (S<-< u)

    abstract
      divby= : ∀ {t u g} → g ◦ f == #[ t ] i h u → divby t u == g
      divby= {O} {u} {g} w with f ∣ #[ 0 ] i h u
      ... | inl (g' , p) = hom-is-epi _ _ _ (p ∙ ! w)
      ... | inr no = ⊥-rec $ no (g , w)
      divby= {1+ t} {u} {g} w with f ∣ #[ 1+ t ] i h u
      ... | inl (g' , p) = hom-is-epi _ _ _ (p ∙ ! w)
      ... | inr no = ⊥-rec $ no (g , w)

      divby-◦ : ∀ t u → f divides #[ t ] i h u → divby t u ◦ f == #[ t ] i h u
      divby-◦ t u (g , p) rewrite divby= p = p

    -- Lemma 6.11 (12.10.23)
    divby-lub : (t : ℕ) (u : t < hom-size i h ) (g : hom j h)
      → g ◦ f ≼ #[ t ] i h u
      → g ≼ divby t u
    divby-lub O u g w = =-≼ (! $ divby= (≼[O] _ _ w))
    divby-lub (1+ t) u g w with f ∣ #[ 1+ t ] i h u
    ... | inl (g' , p) = ≼-cancel-r _ _ _ (transp (_ ≼_) (! p) w)
    ... | inr no with w
    ...          | inl p = ⊥-rec $ no (g , hom= p)
    ...          | inr u = divby-lub t _ _ (≺S-≼ _ _ u)

    -- Lemma 6.12 (12.10.23), and extras
    module smallest-divisible
      (t₀ : ℕ)
      (u : t₀ < hom-size i h)
      (divisible : f divides #[ t₀ ] i h u)
      (smallest : (t : ℕ) (v : t < hom-size i h)
                  → f divides #[ t ] i h v
                  → t₀ ≤ t)
      where
      smallest-divisible-divby : {v : O < hom-size j h}
        → divby t₀ u == #[ O ] j h v
      smallest-divisible-divby {v} = ≼[O] v _ lem'
        where
        p : (divby t₀ u) ◦ f == #[ t₀ ] i h u
        p = divby-◦ t₀ u divisible

        [0] = #[ 0 ] j h v
        [0]◦f = [0] ◦ f
        i₀ = to-ℕ $ idx-of [0]◦f
        w = snd $ idx-of [0]◦f

        f∣[i₀] : f divides #[ i₀ ] i h w
        f∣[i₀] = [0] , ! (hom#-idx [0]◦f)

        q : #[ t₀ ] i h u ≼ [0]◦f
        q = idx≤-≼ _ _ $
          transp (_≤ i₀) (! $ ap to-ℕ (idx-hom# (t₀ , u))) $
          smallest i₀ w f∣[i₀]

        lem : (divby t₀ u) ◦ f ≼ [0]◦f
        lem rewrite p = q

        lem' : divby t₀ u ≼ [0]
        lem' = ≼-cancel-r _ _ _ lem

      divby-◦-ub : (t : ℕ) (v : t < hom-size i h)
        → t₀ ≤ t → divby t v ◦ f ≼ #[ t ] i h v
      divby-◦-ub t v =
        Fin[ hom-size i h ]-ind-from (t₀ , u)
          (λ (t , v) → divby t v ◦ f ≼ #[ t ] i h v)
          (=-≼ (divby-◦ t₀ u divisible))
          ind-case
          (t , v)
        where
        ind-case :
          (t : ℕ)
          (v : 1+ t < hom-size i h)
          (w : (t₀ , u) ≤-Fin (t , S<-< v))
          (ih : (divby t (S<-< v) ◦ f) ≼ #[ t ] i h (S<-< v))
          → divby (1+ t) v ◦ f ≼ #[ 1+ t ] i h v
        ind-case t v w ih with f ∣ #[ 1+ t ] i h v
        ... | inl (_ , p) = =-≼ p
        ... | inr no = inr (≼-≺-≺ ih (#[ t ]≺S (S<-< v) v))

      <-smallest-divisible-divby :
        ∀ t v → (t , v) <-Fin (t₀ , u) → divby t v == #[ O ] j h size-cond
      <-smallest-divisible-divby O v w with f ∣ #[ 0 ] i h v
      ... | inl yes = ⊥-rec $ ¬≤> (t₀ , u) (O , v) (smallest _ _ yes) w
      ... | inr no = idp
      <-smallest-divisible-divby (1+ t) v w with f ∣ #[ 1+ t ] i h v
      ... | inl yes = ⊥-rec $ ¬≤> (t₀ , u) (1+ t , v) (smallest _ _ yes) w
      ... | inr no = <-smallest-divisible-divby t (S<-< v) (S<-< w)

    -- Lemma 6.13 (16.10.23)
    divby-monotone : ∀ t t' u u' → t < t' → divby t u ≼ divby t' u'
    divby-monotone t .(1+ t) u u' ltS =
      case (Fin-trichotomy' t₀ (t , u)) case-t₀≤t case-t<t₀
      where
      open count-factors-properties i h j f

      smallest-divisible =
        let div = hom-size>O-exists-divisible size-cond
        in Fin-smallest-witness (λ (t , u) → f ∣ #[ t ] i h u) (fst div) (snd div)

      t₀ = fst smallest-divisible
      Pt₀ = 2nd smallest-divisible
      t₀-smallest = 3rd smallest-divisible

      open smallest-divisible (fst t₀) (snd t₀) Pt₀ (curry t₀-smallest)

      case-t₀≤t : t₀ ≤-Fin (t , u) → divby t u ≼ divby (1+ t) u'
      case-t₀≤t v = divby-lub (1+ t) u' _ lem
        where lem = ≼-≺-≼ (divby-◦-ub t u v) (#[ t ]≺S u u')

      case-t<t₀ : (t , u) <-Fin t₀ → divby t u ≼ divby (1+ t) u'
      case-t<t₀ v rewrite <-smallest-divisible-divby t u v = [O]-min size-cond _

    divby-monotone t (1+ t') u u' (ltSR v) =
      ≼-trans
        (divby-monotone t t' u (S<-< u') v)
        (divby-monotone t' (1+ t') (S<-< u') u' ltS)

  count-factors-gives-shape :
    ∀ i h t s {j} (f : hom i j)
    → count-factors i h t s f ≤ hom-size j h
  count-factors-gives-shape = {!!}


{- Shape induction -}

Shape = Σ[ (i , h , t) ː ℕ × ℕ × ℕ ] shape i h t
𝑣 : Shape → ℕ
𝑣 = fst ∘ fst

ℎ : Shape → ℕ
ℎ = 2nd ∘ fst

𝑡 : Shape → ℕ
𝑡 = 3rd ∘ fst

is-shape : (((i , h , t) , s) : Shape) → shape i h t
is-shape = snd

_<ₛ_ : Shape → Shape → Type₀
s <ₛ s' = (𝑣 s < 𝑣 s')
        ⊔ ((𝑣 s == 𝑣 s') × (ℎ s < ℎ s'))
        ⊔ ((𝑣 s == 𝑣 s') × (ℎ s == ℎ s') × (𝑡 s < 𝑡 s'))

Shape-accessible : (s : Shape) → is-accessible Shape _<ₛ_ s
Shape-accessible ((i , h , t) , w) = {!!}
