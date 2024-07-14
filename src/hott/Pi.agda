{-# OPTIONS --without-K --rewriting #-}

module hott.Pi where

open import hott.Base public

diagrammatic-comp = _∘_
infixl 80 diagrammatic-comp
syntax diagrammatic-comp g f = f ; g

private
  variable ℓ ℓ₁ ℓ₂ ℓ₃ : ULevel

  module equalities where
    λ=₂ : {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (a : A) → B a → Type ℓ}
          {f g : (a : A) (b : B a) → C a b}
          → (∀ a b → f a b == g a b) → f == g
    λ=₂ P = λ= (λ= ∘ P)

    λ=₃ : {A : Type ℓ₁} {B : Type ℓ₂} {C : A → B → Type ℓ₃} {D : Type ℓ}
          {f g : (a : A) (b : B) → C a b → D}
          → (∀ a b c → f a b c == g a b c) → f == g
    λ=₃ P = λ=₂ (λ a b → λ= (P a b))

  module equivalences {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where
    fwd-transp-Π-dom : ∀ {ℓ₃} {P : B → Type ℓ₃} (e : A ≃ B)
                       → ((b : B) → P b) → (a : A) → P (–> e a)
    fwd-transp-Π-dom e f = f ∘ –> e

    bwd-transp-Π-dom : ∀ {ℓ₃} {P : A → Type ℓ₃} (e : A ≃ B)
                       → ((a : A) → P a) → (b : B) → P (<– e b)
    bwd-transp-Π-dom e f = f ∘ <– e

    inv-equiv : {f : A → B} → is-equiv f → B → A
    inv-equiv {f} e = <– (f , e)

  module reasoning where
    contrapos : {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → ¬ B → ¬ A
    contrapos f ¬b a = ¬b (f a)

open equalities public
open equivalences public
open reasoning public
