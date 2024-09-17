{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

{- Encoding "compatible families of functions"; or, encoding things that almost
look like very dependent types.

This file contains lots of experimental code and possibly half-formed ideas. -}

module experiments.VeryDependent where

open import hott.HoTT

{- The general problem is to construct an A-indexed set of terms bₐ : Bₐ by
induction on some well founded order (A, <), where for each a : A the type Bₐ
"is dependent on" (i.e. may refer to) terms bₓ : Bₓ of previous levels x < a.
-}

module approach1 {ℓ} -- Just assume one universe for now
  (A : Type ℓ) (_<_ : A → A → Type ℓ) (<-is-wf : all-acc A _<_)
  where
  -- A type family over A, where the definition of (M a) is allowed to use given
  -- values vₓ : Vₓ indexed over x : A where x < a.
  M : (a : A) → ((x : A) → x < a → Σ[ V ﹕ Type ℓ ] V) → Type ℓ

  P : (a : A) → Acc A _<_ a → (x : A) → x < a → Σ[ U ﹕ Type ℓ ] U

  -- A function F over A, where the type of (F a) is (M a) with allowed  above.
  F : (a : A) → M a (λ x x<a → P a (<-is-wf a) x x<a)

  M a h = {!!}
  P a (acc .a rec) x x<a = M x (λ y y<x → P x (rec x x<a) y y<x) , F x
  F a = {!!}

module approach2
  where
  -- 05.09.2024
  {- Here we follow the intuition that a very dependent type is like a "pointed
  infinite Σ-type". We call this a "compatible family", .

  Of course, in general this family is indexed by a wellfounded order (A, _<_),
  not necessarily a linear order. -}

  Rstr : ∀ {ℓ} → Type (lsuc ℓ)
  Rstr {ℓ} = Σ[ R ﹕ Type ℓ ] R

  CompatibleFam : ∀ {ℓ} → Type ℓ → Type (lsuc ℓ)
  CompatibleFam {ℓ} A = A → Rstr

  -- A simple ω-indexed example
  module ℕ-CompatibleFam where
    F : CompatibleFam ℕ

    ty : ℕ → Type₀
    tm : (n : ℕ) → ty n
    tm-to-ℕ : ℕ → ℕ

    F O = ty O , tm O
    F (1+ n) = (fst (F n) × ty (1+ n)) , (snd (F n) , tm (1+ n))

    ty n = Fin (1+ (tm-to-ℕ n))
    tm n = tm-to-ℕ n , ltS

    {- This one (only?) works because we can "go to the bottom" and define
    tm-to-ℕ directly by recursion, without mutual recursion with any of the
    other functions F, ty or tm. In particular, the target *type* of this
    function is not defined using the values of any of the other mutually
    defined functions. -}

    tm-to-ℕ O = 0
    tm-to-ℕ (1+ O) = 1
    tm-to-ℕ (2+ n) = tm-to-ℕ (1+ n) + tm-to-ℕ n

    test-ty : fst (F 6) == (((((Fin 1 × Fin 2) × Fin 2) × Fin 3) × Fin 4) × Fin 6) × Fin 9
    test-ty = idp

    test-tm : snd (F 6) == (((((0 , 1) , 1) , 2) , 3) , 5) , 8
    test-tm = idp

    {- In other words, does this work because in some sense all we're doing is
    constructing the element (0, 1, 2, ...) of the *nondependent* stream first,
    and then modifying the type "after the fact"? -}

  -- Can we do the above in general?
  module _ {ℓ}
    (A : Type ℓ) (_<_ : A → A → Type ℓ) (<-is-wf : all-acc A _<_)
    where

    open WellFoundedInduction A _<_ <-is-wf

    F : CompatibleFam A
    F = wf-ind (λ _ → Rstr) {!!}


module example1? where

  -- This (old) example is like the one in ℕ-CompatibleFam above. See the
  -- comments there.

  {- The following defines a sequence of terms b(i), together with their types,
  where b(i) itself is the sequence of numbers
    0 : Fin 1, 1 : Fin 2, ..., i : Fin (i + 1).

  The "infinite Σ-type" seq is "Fin 1 × Fin 2 × ...", and the element is
  (0,1,2,...). -}

  seq : (i : ℕ) → Σ[ B ﹕ Type₀ ] B
  type : ℕ → Type₀
  term : ∀ i → type i
  last-of : ∀ i → type (1+ i) → ℕ

  seq O = Fin 1 , 0
  seq (1+ O) = Fin 1 × Fin 2 , 0 , 1 , ltS
  seq (2+ i) =
    type (1+ i) × Fin (2+ (last-of i (term (1+ i)))) ,
    term (1+ i) , 1+ (last-of i (term (1+ i))) , ltS

  type i = fst (seq i)
  term i = snd (seq i)

  last-of O (_ , n) = to-ℕ n
  last-of (1+ i) (_ , n) = to-ℕ n

  test-type : fst (seq 3) == ((Fin 1 × Fin 2) × Fin 3) × Fin 4
  test-type = idp

  test-term : snd (seq 3) == (((0 , _) , (1 , _)) , (2 , _)) , (3 , _)
  test-term = idp

module example2? where
  seq : (i : ℕ) → Σ[ A ﹕ Type₀ ] A
  type : ℕ → Type₀
  term : ∀ i → type i
  get : ∀ i → type i → ℕ

  seq O = Fin 1 , 0
  seq (1+ O) = Fin 2 , (1 , ltS)
  seq (2+ i) = Fin {!to-ℕ (snd (seq i)) + to-ℕ ?!} , {!!}

  type i = {!!}

  term i = {!!}

  get O = {!!}
  get (1+ i) = {!!}
