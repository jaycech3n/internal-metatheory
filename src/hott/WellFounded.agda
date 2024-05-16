{-# OPTIONS --without-K --rewriting #-}

open import hott.Base

module hott.WellFounded where

module _ {ℓ₁ ℓ₂} (A : Type ℓ₁) (_<_ : A → A → Type ℓ₂) where
  data Acc : A → Type (ℓ₁ ∪ ℓ₂) where
    acc : ∀ a → (∀ b → b < a → Acc b) → Acc a

  open Acc public

  Acc-elim : ∀ {ℓ}
    → (P : (a : A) → Acc a → Type ℓ)
    → (f : (a : A)
         → (h : ∀ b → b < a → Acc b)
         → (f : ∀ b → (u : b < a) → P b (h b u))
         → P a (acc a h) )
    → (a : A) (c : Acc a) → P a c
  Acc-elim P f a (acc .a w) =
    f a w (λ b u → Acc-elim P f b (w b u))

  Acc-rec : ∀ {ℓ}
    → (P : A → Type ℓ)
    → (f : ∀ a → (∀ b → b < a → P b) → P a)
    → ∀ a → Acc a → P a
  Acc-rec P f = Acc-elim (λ a _ → P a) (λ a _ → f a)

  all-acc : Type (ℓ₁ ∪ ℓ₂)
  all-acc = (a : A) → Acc a

  has-wf-ind : ∀ {ℓ} (P : A → Type ℓ) → Type (ℓ₁ ∪ ℓ₂ ∪ ℓ)
  has-wf-ind P = (∀ a → (∀ b → b < a → P b) → P a) → ∀ a → P a

  all-acc-implies-has-wf-ind :
    ∀ {ℓ} (P : A → Type ℓ)
    → all-acc
    → has-wf-ind P
  all-acc-implies-has-wf-ind P h f a = Acc-rec P f a (h a)


module WellFoundedInduction {ℓ₁ ℓ₂}
  (A : Type ℓ₁)
  (_<_ : A → A → Type ℓ₂)
  (c : all-acc A _<_)
  where

  wf-ind : ∀ {ℓ} (P : A → Type ℓ) → has-wf-ind A _<_ P
  wf-ind P = all-acc-implies-has-wf-ind A _<_ P c


-- "Displaying" (?) well founded orders
module _ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') where

  <Σ : ∀ {ℓ''} (_<_ : A → A → Type ℓ'') → Σ A B → Σ A B → Type ℓ''
  <Σ _<_ (a , b) (a' , b') = a < a'

  module _ {ℓ''} (_<_ : A → A → Type ℓ'') where

    <Σ-preserves-Acc :
      ∀ (t : Σ A B)
      → Acc A _<_ (fst t)
      → Acc (Σ A B) (<Σ _<_) t
    <Σ-preserves-Acc t (acc _ rec) =
      acc _ (λ{ t'@(a' , _) a'<a → <Σ-preserves-Acc t' (rec a' a'<a) })

    <Σ-preserves-all-acc :
      all-acc A _<_ → all-acc (Σ A B) (<Σ _<_)
    <Σ-preserves-all-acc all-ac t =
      acc _ λ t' t'<t → <Σ-preserves-Acc t' (all-ac (fst t'))
