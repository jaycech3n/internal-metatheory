{-# OPTIONS --without-K --rewriting #-}

module hott.WellFounded where

open import hott.Base public
open import hott.Pi

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

  acc-irrefl : ∀ a → Acc a → ¬ (a < a)
  acc-irrefl = Acc-rec (λ a → ¬ (a < a)) (λ a ih u → ih a u u)

  acc-irrefl' : ∀ a b → Acc a → b < a → ¬ (a == b)
  acc-irrefl' a b ac u idp = acc-irrefl a ac u

  -- By basically the same argument as acc-irrefl (which in fact follows from this):
  acc-not-<-preds : ∀ a → Acc a → ∀ b → b < a → ¬ (a < b)
  acc-not-<-preds =
    Acc-rec (λ a → ∀ b → b < a → ¬ (a < b)) (λ a ih b u v → ih b u a v u)

  -- Infinite descending <-chain from a
  inf-desc : A → Type _
  inf-desc a = Σ (ℕ → A) λ s → (s 0 < a) × (∀ n → s (S n) < s n)

  no-infinite-descent : ∀ a → Acc a → ¬ (inf-desc a)
  no-infinite-descent =
    Acc-rec (¬ ∘ inf-desc)
      λ{a ih (s , s₀<a , d) → ih (s 0) s₀<a (s ∘ S , d 0 , d ∘ S)}

  Acc-has-all-paths : ∀ a → (c c' : Acc a) → c == c'
  Acc-has-all-paths =
    Acc-elim (λ a c → (c' : Acc a) → c == c') (λ a h f c' → lem a c' h f)
    where
    lem :
      (a : A) (c : Acc a)
      (h : (b : A) → b < a → Acc b)
      (f : (b : A) (u : b < a) (c' : Acc b) → h b u == c')
      → acc a h == c
    lem =
      Acc-elim (λ a c → ∀ h f → acc a h == c)
        λ a h _ h' k → ap (acc a) (λ=₂ λ a' u → k a' u _)

module WellFoundedInduction {ℓ₁ ℓ₂}
  (A : Type ℓ₁)
  (_<_ : A → A → Type ℓ₂)
  (c : all-acc A _<_)
  where

  wf-ind : ∀ {ℓ} (P : A → Type ℓ) → has-wf-ind A _<_ P
  wf-ind P = all-acc-implies-has-wf-ind A _<_ P c

module _ {ℓ ℓ' ℓ″} {A : Type ℓ} {B : Type ℓ'}
  (_<_ : B → B → Type ℓ″) (f : A → B)
  where

  lift-rel : A → A → Type ℓ″
  lift-rel a a' = f a < f a'

  lift-acc : (a : A) → Acc B _<_ (f a) → Acc A lift-rel a
  lift-acc a (acc .(f a) h) = acc a (λ a' h' → lift-acc a' (h (f a') h'))

  lift-wf : all-acc B _<_ → all-acc A lift-rel
  lift-wf ac a = lift-acc a (ac (f a))

-- "Augmenting" well founded orders
module _ {ℓ ℓ' ℓ''} {A : Type ℓ} (_<_ : A → A → Type ℓ'') (B : A → A → Type ℓ')
  where
  <[] : A → A → Type _
  <[] a' a = (a' < a) × B a' a

  <[]-preserves-all-acc : all-acc A _<_ → all-acc A <[]
  <[]-preserves-all-acc ac =
    wf-ind (Acc A <[]) λ a ih → acc a (λ{a' (u , _) → ih a' u})
    where open WellFoundedInduction A _<_ ac

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
