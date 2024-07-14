{-# OPTIONS --without-K --rewriting #-}

module hott.Sigma where

open import hott.Base public
open import hott.Paths public

Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ﹕ A ] B -- use \:9

last-two : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A × B × C → B × C
last-two (_ , b , c) = b , c

-- A bit of an ad-hoc place for this for now
¬uncurry : ∀ {ℓ₁ ℓ₂ ℓ₃}
  → {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (a : A) → B a → Type ℓ₃}
  → ¬ ((a : A) (b : B a) → C a b)
  → ¬ ((p : Σ A B) → C (fst p) (snd p))
¬uncurry ¬f g = ¬f $ curry g

private
  module triples {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂} {C : {a : A} (b : B a) → Type ℓ₃}
    where

    2nd : (u : Σ[ a ﹕ A ] Σ[ b ﹕ B a ] C b) → B (fst u)
    2nd = fst ∘ snd

    3rd : (u : Σ[ a ﹕ A ] Σ[ b ﹕ B a ] C b) → C (2nd u)
    3rd = snd ∘ snd

    first-two : Σ[ a ﹕ A ] Σ[ b ﹕ B a ] C b → Σ[ a ﹕ A ] B a
    first-two (a , b , _) = a , b

  module assoc {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (a : A) (b : B a) → Type ℓ₃}
    where
    Σ-fwd-assoc : Σ (Σ A B) (uncurry C) → Σ A (λ a → Σ (B a) (C a))
    Σ-fwd-assoc ((a , b) , c) = (a , (b , c))

    Σ-bwd-assoc : Σ A (λ a → Σ (B a) (C a)) → Σ (Σ A B) (uncurry C)
    Σ-bwd-assoc (a , (b , c)) = ((a , b) , c)

  module equivalences {ℓ₁ ℓ₂} where
    -- Old:
    -- Σ-fmap-dom-fwd : {C : B → Type ℓ₃} → Σ B C → Σ A (C ∘ –> e)
    -- Σ-fmap-dom-fwd {C} (b , c) = <– e b , transp C (! (<–-inv-r e b)) c

    Σ-emapf-dom :
      {A B : Type ℓ₁} (C : A → Type ℓ₂)
      → (e : A ≃ B) → Σ A C → Σ B (C ∘ <– e)
    Σ-emapf-dom C e (a , c)= –> e a , transp C (! (<–-inv-l e a)) c

    Σ-emapf-dom-is-equiv :
      {A B : Type ℓ₁} (C : A → Type ℓ₂)
      → (e : A ≃ B) → is-equiv (Σ-emapf-dom C e)
    Σ-emapf-dom-is-equiv C e = is-eq f g f-g g-f
      where
      f = Σ-emapf-dom C e
      g = λ {(b , c) → (<– e b) , c}

      f-g : ∀ y → f (g y) == y
      f-g (b , c) = let p = <–-inv-r e b in
        pair= p
        $ from-transp! _ p
            (transp-family-precomp-equiv e b c
            ∙ transp!=transport! p)

      g-f : ∀ x → g (f x) == x
      g-f (a , c) =
        pair= (<–-inv-l e a) $
          from-transp! _ (<–-inv-l e a) $
            transp!=transport! (<–-inv-l e a)

    Σ-emape-dom :
      {A B : Type ℓ₁} (C : A → Type ℓ₂)
      → (e : A ≃ B)
      → Σ A C ≃ Σ B (C ∘ <– e)
    Σ-emape-dom C e = Σ-emapf-dom C e , Σ-emapf-dom-is-equiv C e

    Σ-contr-dom :
      {A : Type ℓ₁} {B : A → Type ℓ₂} -- (a₀ : A)
      → (c : is-contr A) -- ((x : A) → x == a₀)
      → Σ A B ≃ B (contr-center c) -- a₀
    Σ-contr-dom {A} {B} c@(has-level-in (a₀ , p)) = f , is-eq f g f-g g-f
      where
      f : Σ A B → B a₀
      f (a , b) = transp! B (p a) b

      g : B a₀ → Σ A B
      g b = a₀ , b

      f-g : (b : B a₀) → f (g b) == b
      f-g b = app= (ap (transp! B)
        (prop-path (=-preserves-level (contr-has-level c)) _ _)) b
        -- not sure why the instance search doesn't work any more

      g-f : (a : Σ A B) → g (f a) == a
      g-f (a , b) =
        pair= (p a) $
          from-transp _ (p a) $
            ! (transp-∙ (! (p a)) (p a) b)
            ∙ app= (ap (transp B) (!-inv-l (p a))) b

open triples public
open assoc public
open equivalences public
