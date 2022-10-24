{-# OPTIONS --without-K #-}

module hott.Sigma where

open import hott.Base public

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∶ A ] B -- use \:

private
  module triples {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} (b : B a) → Type ℓ₃}
    where

    2nd : (u : Σ[ a ∶ A ] Σ[ b ∶ B a ] C b) → B (fst u)
    2nd = fst ∘ snd

    3rd : (u : Σ[ a ∶ A ] Σ[ b ∶ B a ] C b) → C (2nd u)
    3rd = snd ∘ snd

  module equivalences {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} (e : A ≃ B) where
    fwd-transp-Σ-dom : {C : B → Type ℓ₃} → Σ[ b ∶ B ] C b → Σ[ a ∶ A ] C (–> e a)
    fwd-transp-Σ-dom {C} (b , c) = <– e b , transp C (! (<–-inv-r e b)) c

    bwd-transp-Σ-dom : {C : A → Type ℓ₃} → Σ[ a ∶ A ] C a → Σ[ b ∶ B ] C (<– e b)
    bwd-transp-Σ-dom {C} (a , c)= –> e a , transp C (! (<–-inv-l e a)) c

open triples public
open equivalences public
