{-# OPTIONS --without-K --rewriting #-}

open import hott.Base

module hott.Induction where

module _ {ℓ₁ ℓ₂} (A : Type ℓ₁) (_<_ : A → A → Type ℓ₂) where
  data is-accessible : A → Type (ℓ₁ ∪ ℓ₂) where
    acc : ∀ {a} → (∀ b → b < a → is-accessible b) → is-accessible a

  open is-accessible public

  is-accessible-elim : ∀ {ℓ}
    → (P : (a : A) → is-accessible a → Type ℓ)
    → (f : (a : A)
         → (h : ∀ b → b < a → is-accessible b)
         → (f : ∀ b → (u : b < a) → P b (h b u))
         → P a (acc h) )
    → (a : A) (c : is-accessible a) → P a c
  is-accessible-elim P f a (acc w) =
    f a w (λ b u → is-accessible-elim P f b (w b u))

  is-accessible-rec : ∀ {ℓ}
    → (P : A → Type ℓ)
    → (f : ∀ a → (∀ b → b < a → P b) → P a)
    → ∀ a → is-accessible a → P a
  is-accessible-rec P f = is-accessible-elim (λ a _ → P a) (λ a _ → f a)

  all-accessible : Type (ℓ₁ ∪ ℓ₂)
  all-accessible = (a : A) → is-accessible a

  has-wf-ind : ∀ {ℓ} (P : A → Type ℓ) → Type (ℓ₁ ∪ ℓ₂ ∪ ℓ)
  has-wf-ind P = (∀ a → (∀ b → b < a → P b) → P a) → ∀ a → P a

  all-accessible-implies-has-wf-ind :
    ∀ {ℓ} (P : A → Type ℓ)
    → all-accessible
    → has-wf-ind P
  all-accessible-implies-has-wf-ind P h f a = is-accessible-rec P f a (h a)

module WellFoundedInduction {ℓ₁ ℓ₂}
  (A : Type ℓ₁)
  (_<_ : A → A → Type ℓ₂)
  (c : all-accessible A _<_)
  where

  wf-ind : ∀ {ℓ} (P : A → Type ℓ) → has-wf-ind A _<_ P
  wf-ind P = all-accessible-implies-has-wf-ind A _<_ P c


-- The transitive closure of a wellfounded relation is wellfounded.

module TransitiveClosure {ℓ₀ ℓ₁} {A : Type ℓ₀} (R : A → A → Type ℓ₁) where

  data TransClosure : A → A → Type (ℓ₀ ∪ ℓ₁) where
    [_]⁺ : {a b : A} → R a b → TransClosure a b
    _∷⁺_ : {a b c : A} → R a b → TransClosure b c → TransClosure a c

  infixr 4 _++⁺_

  R⁺ = TransClosure

  -- The transitive closure is transitive
  _++⁺_ : ∀ {a b c} → R⁺ a b → R⁺ b c → R⁺ a c
  [ a↝b ]⁺ ++⁺ b↝c = a↝b ∷⁺ b↝c
  (a↝b₀ ∷⁺ b₀↝b) ++⁺ b↝c = a↝b₀ ∷⁺ (b₀↝b ++⁺ b↝c)

module TransWellFounded {ℓ₀ ℓ₁} {A : Type ℓ₀} (R : A → A → Type ℓ₁) (R-is-wf : all-accessible A R) where

  open TransitiveClosure R

  -- Nicolai: I had originally formalised this for https://arxiv.org/abs/2107.01594
  -- see: https://www.cs.nott.ac.uk/~psznk/agda/confluence/

  multiple-steps : ∀ {a c} → R⁺ c a → (∀ b → R b a → is-accessible A R⁺ b) → is-accessible A R⁺ c
  multiple-steps [ c<a ]⁺ ih = ih _ c<a
  multiple-steps (c<c₁ ∷⁺ c₁<⁺a) ih with multiple-steps c₁<⁺a ih
  multiple-steps (c<c₁ ∷⁺ c₁<⁺a) ih | acc <c₁-is-acc = <c₁-is-acc _ [ c<c₁ ]⁺

  trans-closure-wf : all-accessible A R⁺
  trans-closure-wf = all-accessible-implies-has-wf-ind A R (is-accessible A R⁺) R-is-wf
                       λ a ih → acc λ c p → multiple-steps p ih


