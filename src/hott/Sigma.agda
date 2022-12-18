{-# OPTIONS --without-K --rewriting #-}

module hott.Sigma where

open import hott.Base public

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ː A ] B -- use \:3

last-two : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → A × B × C → B × C
last-two (_ , b , c) = b , c

private
  module triples {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} (b : B a) → Type ℓ₃}
    where

    2nd : (u : Σ[ a ː A ] Σ[ b ː B a ] C b) → B (fst u)
    2nd = fst ∘ snd

    3rd : (u : Σ[ a ː A ] Σ[ b ː B a ] C b) → C (2nd u)
    3rd = snd ∘ snd

    first-two : Σ[ a ː A ] Σ[ b ː B a ] C b → Σ[ a ː A ] B a
    first-two (a , b , _) = a , b

  module equivalences {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (e : A ≃ B) where
    fwd-transp-Σ-dom : {C : B → Type ℓ₃} → Σ[ b ː B ] C b → Σ[ a ː A ] C (–> e a)
    fwd-transp-Σ-dom {C} (b , c) = <– e b , transp C (! (<–-inv-r e b)) c

    bwd-transp-Σ-dom : {C : A → Type ℓ₃} → Σ[ a ː A ] C a → Σ[ b ː B ] C (<– e b)
    bwd-transp-Σ-dom {C} (a , c)= –> e a , transp C (! (<–-inv-l e a)) c

open triples public
open equivalences public
