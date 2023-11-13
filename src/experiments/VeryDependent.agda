{-# OPTIONS --without-K --rewriting #-}

{- Encoding "compatible families of functions"; or, encoding things that almost
look like very dependent types. -}

module experiments.VeryDependent where

open import hott.HoTT

{- Technique?

The general problem is that we want to construct a sequence of terms b : B by
induction on some well-order, whose types B are dependent on terms b of previous
levels. -}

{- e.g. The following defines a sequence of terms b(i) (together with their types) where
b(i) = 0 : Fin 1, 1 : Fin 2, ..., i : Fin (i + 1) -}

Constr : (i : ℕ) → Σ[ B ː Type₀ ] B
last : (i : ℕ) → fst (Constr (1+ i)) → ℕ

-- type : ℕ → Type₀
-- term : ∀ i → type i

-- type O = fst (Constr O)
-- type (1+ i) = fst (Constr (1+ i))

-- term O = snd (Constr O)
-- term (1+ i) = snd (Constr (1+ i))

Constr O = Fin 1 , 0
Constr (1+ O) = Fin 1 × Fin 2 , 0 , 1 , ltS
Constr (2+ i) =
  fst (Constr (1+ i)) × Fin (2+ (last i (snd (Constr (1+ i))))) ,
  snd (Constr (1+ i)) , 1+ (last i (snd (Constr (1+ i)))) , ltS

last O = to-ℕ ∘ snd
last (1+ i) = to-ℕ ∘ snd

test-type : fst (Constr 3) == ((Fin 1 × Fin 2) × Fin 3) × Fin 4
test-type = idp

test-term : snd (Constr 3) == (((0 , _) , (1 , _)) , (2 , _)) , (3 , _)
test-term = idp

-- For convenience:
infixl 80 _×ₗ_
infixl 60 _,ₗ_

_×ₗ_ : ∀ {i j} → Type i → Type j → Type (i ∪ j)
A ×ₗ B = A × B

_,ₗ_ : ∀ {i j} {A : Type i} {B : Type j} → A → B → A ×ₗ B
a ,ₗ b = a , b
