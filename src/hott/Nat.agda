{-# OPTIONS --without-K --rewriting #-}

module hott.Nat where

open import hott.Base public

pattern 1+ n = S n
pattern 2+ n = S (S n)

<= : ∀ {m n} (u u' : m < n) → u == u'
<= = prop-path <-is-prop

instance
  ℕ-id-is-prop : {m n : ℕ} → is-prop (m == n)
  ℕ-id-is-prop = has-level-apply ℕ-is-set _ _

_>_ : ℕ → ℕ → Type₀
m > n = n < m

module Nat-trichotomy where
  abstract
    ℕ-trichotomy' : (m n : ℕ) → (m ≤ n) ⊔ (n < m)
    ℕ-trichotomy' m n with ℕ-trichotomy m n
    ... | inl m=n = inl (inl m=n)
    ... | inr (inl m<n) = inl (inr m<n)
    ... | inr (inr n<m) = inr n<m

open Nat-trichotomy public

module Nat-ad-hoc-lemmas where

  {- One arg -}

  module _ {n} where
    ¬<-self : ¬ (n < n)
    ¬<-self u = <-to-≠ u idp

    <1-=O : n < 1 → n == O
    <1-=O ltS = idp

    ≤O-=O : n ≤ O → n == O
    ≤O-=O (inl idp) = idp

  O<-witness : ∀ {n} → O < n → Σ ℕ λ m → 1+ m == n
  O<-witness ltS = O , idp
  O<-witness (ltSR u) = 1+ (fst $ O<-witness u) , (ap 1+ $ snd (O<-witness u))

  S≮ : ∀ {n} → ¬ (S n < n)
  S≮ {O} ()
  S≮ {1+ n} = S≮ ∘ <-cancel-S

  S≰ : ∀ {n} → ¬ (S n ≤ n)
  S≰ {O} = S≰O _
  S≰ {1+ n} = S≰ ∘ ≤-cancel-S

  ¬O<-=O : ∀ n → ¬ (O < n) → n == O
  ¬O<-=O O u = idp
  ¬O<-=O (1+ n) u = ⊥-rec (u (O<S n))

  O<¬=O : ∀ n → O < n → ¬ (n == O)
  O<¬=O n u idp = ¬<-self u

  ¬=O-O< : ∀ n → ¬ (n == O) → O < n
  ¬=O-O< O u = ⊥-rec (u idp)
  ¬=O-O< (1+ n) u = O<S n

  {- Two args -}

  module _ {m n} where
    =-cancel-S : 1+ m == 1+ n :> ℕ → m == n
    =-cancel-S idp = idp

    <-O< : m < n → O < n
    <-O< ltS = O<S m
    <-O< (ltSR u) = O<S _

    <S-≤ : m < 1+ n → m ≤ n
    <S-≤ ltS = lteE
    <S-≤ (ltSR u) = inr u

    <-S≤ : m < n → 1+ m ≤ n
    <-S≤ ltS = lteE
    <-S≤ (ltSR u) = inr (<-ap-S u)

    S≤-< : 1+ m ≤ n → m < n
    S≤-< (inl idp) = ltS
    S≤-< (inr u) = <-trans ltS u

    S<-< : 1+ m < n → m < n
    S<-< = S≤-< ∘ inr -- <-trans ltS u

    S≤-≤ : 1+ m ≤ n → m ≤ n
    S≤-≤ = inr ∘ S≤-< -- ≤-trans lteS

    <-witness' : m < n → Σ ℕ (λ k → k + m == n)
    <-witness' u = let w = <-witness u in 1+ (fst w) , snd w

    abstract
      no-between : m < n → n < 1+ m → ⊥
      no-between u v with <-S≤ u
      ... | inl idp = ¬<-self v
      ... | inr w = ¬<-self (<-trans v w)

      ≰-to-> : ¬ (m ≤ n) → n < m
      ≰-to-> ¬m≤n with ℕ-trichotomy' m n
      ... | inl m≤n = ⊥-rec $ ¬m≤n m≤n
      ... | inr n<m = n<m

      ≮-to-≥ : ¬ (m < n) → n ≤ m
      ≮-to-≥ m≮n with ℕ-trichotomy' n m
      ... | inl n≤m = n≤m
      ... | inr m<n = ⊥-rec $ m≮n m<n

    ≤-to-≯ : m ≤ n → ¬ (n < m)
    ≤-to-≯ (inl idp) n<m = ¬<-self n<m
    ≤-to-≯ (inr m<n) n<m = ¬<-self (<-trans m<n n<m)

    ≤-between-= : m ≤ n → n ≤ m → m == n
    ≤-between-= (inl idp) v = idp
    ≤-between-= (inr u) (inl idp) = idp
    ≤-between-= (inr u) (inr v) = ⊥-rec $ ¬<-self (<-trans u v)

  S≤-1≤ : ∀ {m n} → 1+ m ≤ n → 1 ≤ n
  S≤-1≤ {m} {O} u = ⊥-rec (S≰O m u)
  S≤-1≤ {m} {1+ n} u = ≤-ap-S (O≤ n)

  ≤-+-mid : ∀ {m n} → 1+ m ≤ 1+ (n + m)
  ≤-+-mid {m} {O} = lteE
  ≤-+-mid {m} {1+ n} = lteSR $ ≤-+-mid {m} {n}

  <1+ : ∀ {m n} → n < 1+ m + n
  <1+ {O} = ltS
  <1+ {1+ m} = <-trans (<1+ {m}) ltS

  {- Three args -}

  module _ {k m n} where
    ≤-<-< : k ≤ m → m < n → k < n
    ≤-<-< (inl idp) u' = u'
    ≤-<-< (inr u) u' = <-trans u u'

    <-≤-< : k < m → m ≤ n → k < n
    <-≤-< u (inl idp) = u
    <-≤-< u (inr u') = <-trans u u'

    <-≤-≤ : k < m → m ≤ n → k ≤ n
    <-≤-≤ u u' = inr (<-≤-< u u')

    3-comm-2 : k + m + n == m + k + n
    3-comm-2 = +-comm k m |in-ctx (_+ n)

  +-≤-dropl : ∀ {m n k} → m + n ≤ k → n ≤ k
  +-≤-dropl {O} {n} {k} u = u
  +-≤-dropl {1+ m} {n} {k} u = +-≤-dropl (S≤-≤ u)

  {- Four args -}

  <-+ : ∀ {k l m n} → k < m → l < n → k + l < m + n
  <-+ {k} ltS u' = ltSR (<-+-l k u')
  <-+ (ltSR u) ltS = ltSR (<-+ u ltS)
  <-+ (ltSR u) (ltSR u') = ltSR (<-+ u (<-trans u' ltS))

  ≤-+ : ∀ {k l m n} → k ≤ m → l ≤ n → k + l ≤ m + n
  ≤-+ {k} (inl idp) u' = ≤-+-l k u'
  ≤-+ {l = l} (inr u) (inl idp) = inr (<-+-r l u)
  ≤-+ (inr u) (inr u') = inr (<-+ u u')

  +-assocr-≤ : ∀ {k} l m n → l + m + n ≤ k → l + (m + n) ≤ k
  +-assocr-≤ {k} l m n u = transp (_≤ k) (+-assoc l m n) u

  +-assocl-≤ : ∀ {k} l m n → l + (m + n) ≤ k → l + m + n ≤ k
  +-assocl-≤ {k} l m n u = transp (_≤ k) (! (+-assoc l m n)) u

  +-comm-≤ : ∀ {k} m n → m + n ≤ k → n + m ≤ k
  +-comm-≤ {k} m n = transp (_≤ k) (+-comm m n)

open Nat-ad-hoc-lemmas public

module Nat-predecessor where
  infix 999 _−1
  _−1 : ℕ → ℕ
  O −1 = O
  (1+ n) −1 = n

  −1≤ : ∀ {n} → n −1 ≤ n
  −1≤ {O} = lteE
  −1≤ {1+ n} = lteS

open Nat-predecessor public

module Nat-monus where
  infixl 80 _∸_
  _∸_ : ℕ → ℕ → ℕ
  O ∸ n = O
  1+ m ∸ O = 1+ m
  1+ m ∸ 1+ n = m ∸ n

  ∸-unit-r : ∀ n → n ∸ O == n
  ∸-unit-r O = idp
  ∸-unit-r (1+ n) = idp

  S∸ : ∀ n → 1+ n ∸ n == 1
  S∸ O = idp
  S∸ (1+ n) = S∸ n

  ∸-nonzero : ∀ {m n} → n < m → O < m ∸ n
  ∸-nonzero {1+ m} {.m} ltS rewrite S∸ m = O<S _
  ∸-nonzero {1+ m} {O} (ltSR u) = O<S _
  ∸-nonzero {1+ m} {1+ n} (ltSR u) = ∸-nonzero (<-trans ltS u)

  abstract
    <∸-+< : ∀ {k m} n → k < m ∸ n → k + n < m
    <∸-+< {k} {1+ m} O u rewrite +-unit-r k = u
    <∸-+< {k} {1+ m} (1+ n) u = transp (_< 1+ m) (! (+-βr k n)) (<-ap-S (<∸-+< n u))

  ∸=S-∸S= : ∀ {k} m n → m ∸ n == 1+ k → m ∸ 1+ n == k
  ∸=S-∸S= (1+ m) (1+ n) u = ∸=S-∸S= m n u
  ∸=S-∸S= (1+ O) O u = =-cancel-S u
  ∸=S-∸S= (2+ m) O u = =-cancel-S u

  β∸1 : ∀ {n} → O < n → n == 1+ (n ∸ 1)
  β∸1 {.1} ltS = idp
  β∸1 {1+ n} (ltSR _) rewrite ∸-unit-r n = idp

open Nat-monus public


module Nat-subtraction where
  infixl 80 _−_
  _−_ : (m n : ℕ) → ⦃ n ≤ m ⦄ → ℕ -- should make this use a decidable guard predicate
  (m − .m) ⦃ inl idp ⦄ = O
  (.(1+ n) − n) ⦃ inr ltS ⦄ = 1
  ((1+ m) − n) ⦃ inr (ltSR u) ⦄ = 1+ ((m − n) ⦃ inr u ⦄)

open Nat-subtraction public


module Nat-reasoning where
  ℕ-ind : ∀ {ℓ} (P : ℕ → Type ℓ) → P O → (∀ n → P n → P (1+ n)) → ∀ n → P n
  ℕ-ind P P₀ Pₛ O = P₀
  ℕ-ind P P₀ Pₛ (1+ n) = Pₛ n (ℕ-ind P P₀ Pₛ n)

  ℕ-ind-from : ∀ {ℓ} (n₀ : ℕ) (P : ℕ → Type ℓ)
    → P n₀
    → (∀ n → n₀ ≤ n → P n → P (1+ n))
    → ∀ n → n₀ ≤ n → P n
  ℕ-ind-from n₀ P P₀ Pₛ n (inl idp) = P₀
  ℕ-ind-from n₀ P P₀ Pₛ (1+ n) (inr u) =
    let n₀≤n = <S-≤ u in
    Pₛ n n₀≤n (ℕ-ind-from n₀ P P₀ Pₛ n n₀≤n)
    -- definitionally equal to Pₛ "up to equality of <-witness"

  ℕ-case : ∀ {ℓ} (P : ℕ → Type ℓ) (n : ℕ)
    → (n == O → P O)
    → (∀ m → n == 1+ m → P (1+ m))
    → P n
  ℕ-case P O P₀ Pₛ = P₀ idp
  ℕ-case P (1+ n) P₀ Pₛ = Pₛ n idp

open Nat-reasoning public


module Nat-instances {n : ℕ} where
  -- All instance declarations here will be visible to any module that imports
  -- hott.Nat (this is apparently intended behavior, see GitHub issue #1265)
  instance
    O<S-inst : O < 1+ n
    O<S-inst = O<S n
