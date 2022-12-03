{-# OPTIONS --without-K #-}

module hott.Fin where

open import hott.Base public
open import hott.Conditionals public
open import hott.Nat public
open import hott.Sigma public

to-ℕ : ∀ {n} → Fin n → ℕ
to-ℕ = fst

1+Fin : ∀ {n} ((m , _) : Fin n) → 1+ m < n → Fin n
1+Fin (m , _) h = 1+ m , h

Fin= : ∀ {n} {i j : Fin n} → to-ℕ i == to-ℕ j → i == j
Fin= {_} {.(fst j) , fstj<n} {j} idp = pair= idp (prop-path <-is-prop _ _)

Fin=-is-prop : ∀ {n} {i j : Fin n} → is-prop (i == j)
Fin=-is-prop {_} {i} {j} = has-level-apply Fin-is-set i j

Fin1-is-prop : is-prop (Fin 1)
has-level-apply Fin1-is-prop (i , i<1) (j , j<1) =
  has-level-in (Fin= (<1-=O i<1 ∙ ! (<1-=O j<1)) , λ p → prop-path Fin=-is-prop _ _)

Fin1-has-all-paths : has-all-paths (Fin 1)
Fin1-has-all-paths i j = prop-path Fin1-is-prop _ _

Fin=-elim : ∀ {n} {i j : Fin n} → i == j → fst i == fst j
Fin=-elim {n} {_ , _} {.(_ , _)} idp = idp

_<-Fin_ : ∀ {n} (i j : Fin n) → Type₀
i <-Fin j = to-ℕ i < to-ℕ j

_≤-Fin_ : ∀ {n} (i j : Fin n) → Type₀
i ≤-Fin j = to-ℕ i ≤ to-ℕ j

_<?-Fin_ : ∀ {n} → Decidable (_<-Fin_ {n})
(i , _) <?-Fin (j , _) = i <? j

_≤?-Fin_ : ∀ {n} → Decidable (_≤-Fin_ {n})
(i , _) ≤?-Fin (j , _) = i ≤? j

≤-Fin-trans : ∀ {n} {i j k : Fin n} → i ≤-Fin j → j ≤-Fin k → i ≤-Fin k
≤-Fin-trans (inl idp) (inl idp) = inl idp
≤-Fin-trans (inr u) (inl idp) = inr u
≤-Fin-trans (inl idp) (inr v) = inr v
≤-Fin-trans (inr u) (inr v) = inr (<-trans u v)

abstract
  Fin-trichotomy : ∀ {k} (i j : Fin k) → (i == j) ⊔ (i <-Fin j) ⊔ (j <-Fin i)
  Fin-trichotomy (m , m<k) (n , n<k) = Fin-trichotomy-aux m n m<k n<k
    where
    Fin-trichotomy-aux : ∀ {k} (m n : ℕ) (m<k : m < k) (n<k : n < k)
                         →   ((m , m<k) == (n , n<k))
                           ⊔ ((m , m<k) <-Fin (n , n<k))
                           ⊔ ((n , n<k) <-Fin (m , m<k))
    Fin-trichotomy-aux O O _ _ = inl (Fin= idp)
    Fin-trichotomy-aux O (1+ n) _ _ = inr (inl (O<S n))
    Fin-trichotomy-aux (1+ m) O _ _ = inr (inr (O<S m))
    Fin-trichotomy-aux (1+ m) (1+ n) Sm<k Sn<k
     with Fin-trichotomy-aux m n (<-trans ltS Sm<k) (<-trans ltS Sn<k)
    ... | inl m=n = inl (Fin= (ap S (Fin=-elim m=n)))
    ... | inr (inl m<n) = inr (inl (<-ap-S m<n))
    ... | inr (inr n<m) = inr (inr (<-ap-S n<m))

-- Proof by enumeration
module Fin-decidability where
  ∀-Fin-extend : ∀ {ℓ} {n} {P : Fin (1+ n) → Type ℓ}
                 → ((i : Fin n) → P (Fin-S i))
                 → P (n , ltS)
                 → ∀ i → P i
  ∀-Fin-extend {n = O} {P} _ PO _ = transp P (Fin1-has-all-paths _ _) PO
  ∀-Fin-extend {n = 1+ n} {P} f PSn (i , i<) =
     case (<S-≤ i<)
          (λ{ idp → transp P (Fin= idp) PSn })
          (λ i<Sn → transp P (Fin= idp) (f (i , i<Sn)))

  ∀-Fin? : ∀ {ℓ} {n} (P : Fin n → Type ℓ)
           → ((i : Fin n) → Dec (P i))
           → Dec ((i : Fin n) → P i)
  ∀-Fin? {n = O} P _ = inl (λ ())
  ∀-Fin? {n = 1+ n} P ∀Fin-Sn-Dec-P =
   if ∀-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S) then (λ ∀Fin-n-P →
     if ∀Fin-Sn-Dec-P (n , ltS) then (λ Pn →
       inl (∀-Fin-extend ∀Fin-n-P Pn))
     else λ ¬Pn →
       inr λ ∀Fin-Sn-P → ¬Pn (∀Fin-Sn-P (n , ltS)))
   else λ ¬∀Fin-n-P →
     inr λ ∀Fin-Sn-P → ¬∀Fin-n-P (∀Fin-Sn-P ∘ Fin-S)

  Σ-Fin? : ∀ {ℓ} {n} (P : Fin n → Type ℓ)
           → ((i : Fin n) → Dec (P i))
           → Dec (Σ[ i ː Fin n ] P i)
  Σ-Fin? {n = 0} _ _ = inr (λ ())
  Σ-Fin? {n = 1} P ∀Fin-Sn-Dec-P =
    if (∀Fin-Sn-Dec-P 0)
       (λ  P0 → inl (0 , P0))
       (λ ¬P0 → inr λ{ ((O , ltS) , P0) → ¬P0 P0
                     ; ((1+ _ , ltSR ()) , _)})
  Σ-Fin? {n = 2+ n} P ∀Fin-Sn-Dec-P =
    if Σ-Fin? (P ∘ Fin-S) (∀Fin-Sn-Dec-P ∘ Fin-S) then (λ{ (i , Pi) →
      inl ((Fin-S i) , Pi) })
    else λ ¬ΣFin-n-P →
      if ∀Fin-Sn-Dec-P (1+ n , ltS) then (λ PSn →
        inl ((1+ n , ltS) , PSn))
      else (λ ¬PSn →
        inr λ{ ((i , i<2+n) , Pi) →
               ⊔-elim
                 (λ i≤Sn →
                   ⊔-elim
                     (λ i=Sn → ¬PSn (transp P (Fin= i=Sn) Pi))
                     (λ i<Sn → ¬ΣFin-n-P ((i , i<Sn) , (transp P (Fin= idp) Pi)))
                     i≤Sn)
                 (λ Sn<i → ¬< (≤-<-< (<-S≤ Sn<i) i<2+n))
                 (ℕ-trichotomy' i (1+ n)) })

  -- Deciding fibers of maps between finite types
  Fin-hfiber-dec : ∀ {m n} (f : Fin m → Fin n) (j : Fin n) → Dec (hfiber f j)
  Fin-hfiber-dec {O} {n} f j = inr ((≮O _) ∘ snd ∘ fst)
  Fin-hfiber-dec {1+ m} {n} f j =
    if Fin-hfiber-dec (f ∘ Fin-S) j then
      (λ{ (x@(i , i<m) , fi=j) → inl (Fin-S x , ap f (Fin= idp) ∙ fi=j) })
    else λ h →
      if f (m , ltS) ≟-Fin j then
        (λ fm=j → inl ((m , ltS) , fm=j))
      else λ fm≠j →
        inr λ{ ((i , i<Sm) , fi=j) →
               ⊔-elim
                 (λ i=m → fm≠j (ap f (Fin= (! i=m)) ∙ fi=j))
                 (λ i<m → h ((i , i<m) , ap f (Fin= idp) ∙ fi=j))
                 (<S-≤ i<Sm) }

open Fin-decidability public

module Fin-counting where
  -- The number of (k : Fin n) in the range [i, j) satisfying P.
  #-Fin_from_to_,_and_st :
    ∀ {ℓ} n (i : Fin n) (j : ℕ) (v : j ≤ n)
    → to-ℕ i < j
    → (P : Fin n → Type ℓ) → ((i : Fin n) → Dec (P i))
    → ℕ
  #-Fin n from i to .(1+ (to-ℕ i)) , _ and ltS st P P? =
    if P? i then (λ _ → 1)
    else (λ _ → O)
  #-Fin n from i to 1+ j , v and ltSR u st P P? =
    #-Fin n from i to j , <-≤-≤ ltS v and u st P P?
      + #-Fin n from j , S≤-< v to 1+ j , v and ltS st P P?

  #-Fin-range-1 :
    ∀ {ℓ} n (i : Fin n) (u : 1+ (to-ℕ i) ≤ n)
      (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
    → #-Fin n from i to 1+ (to-ℕ i) , u and ltS st P P? ≤ 1
  #-Fin-range-1 n i u P P? with P? i
  ... | inl _ = lteE
  ... | inr _ = O≤ _

  abstract
    #-Fin-ub :
      ∀ {ℓ} n (i : Fin n) (j : ℕ) (v : j ≤ n) (u : to-ℕ i < j)
        (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
      → to-ℕ i + #-Fin n from i to j , v and u st P P? ≤ j
    #-Fin-ub n i .(1+ (to-ℕ i)) v ltS P P? =
      ≤-+-l (to-ℕ i) (#-Fin-range-1 n _ v P P?)
      ◂$ transp (to-ℕ i + #-Fin n from i to 1+ (to-ℕ i) , v and ltS st P P? ≤_)
                (+-comm (to-ℕ i) 1)
    #-Fin-ub n i (1+ j) v (ltSR u) P P? =
      +-assoc-≤
        (to-ℕ i)
        (#-Fin n from i to j , <-≤-≤ ltS v and u st P P?)
        (#-Fin n from j , S≤-< v to 1+ j , v and ltS st P P?)
      $ ≤-trans
          (≤-+ (#-Fin-ub n i j _ u P P?) (#-Fin-range-1 n _ v P P?))
          (inl (+-comm j 1))

    #-Fin-lb :
      ∀ {ℓ} n (O<n : O < n) (j : ℕ) (v : j ≤ n) (u : O < j)
        (P : Fin n → Type ℓ) (P? : (i : Fin n) → Dec (P i))
      → ((k : Fin n) → to-ℕ k < j → P k)
      → j ≤ #-Fin n from (O , O<n) to j , v and u st P P?
    #-Fin-lb n O<n .1 v ltS P P? all-P with P? (O , O<n)
    ... | inl _ = lteE
    ... | inr ¬PO = ⊥-rec (¬PO (all-P _ ltS))
    #-Fin-lb n O<n (1+ j) v (ltSR u) P P? all-P =
      +-comm-≤ j 1
        (≤-+ (#-Fin-lb n O<n j (<-≤-≤ ltS v) u P P? all-P') Pj-lem)
      where
        all-P' : (k : Fin n) → to-ℕ k < j → P k
        all-P' k = all-P k ∘ ltSR

        Pj-lem : 1 ≤ if P? (j , S≤-< v) then (λ _ → 1) else (λ _ → O)
        Pj-lem with P? (j , S≤-< v)
        ... | inl _ = lteE
        ... | inr ¬Pj = ⊥-rec (¬Pj (all-P _ ltS))

open Fin-counting public

monotone-on-Fin : ∀ {ℓ} {n} → (P : Fin n → Type ℓ) → Type ℓ
monotone-on-Fin P = ∀ i j → i ≤-Fin j → P i → P j

{-
#-Fin-monotone :
  ∀ {ℓ} {n}
  → (P : Fin n → Type ℓ) (dec : (i : Fin n) → Dec (P i)) → monotone-on-Fin P
  → ∀ i j → i ≤-Fin j
  → fst (#-Fin-from i st P dec) ≤ fst (#-Fin-from j st P dec)
#-Fin-monotone {n = n} P dec mono i j (inl idp) =
  transp (λ ◻ → fst (#-Fin-from ◻ st P dec) ≤ fst (#-Fin-from j st P dec)) (Fin= idp) (lteE)
#-Fin-monotone {n = n} P dec mono i@(m , m<n) j@(m' , m'<n) (inr m<m') = {!!}
-}
