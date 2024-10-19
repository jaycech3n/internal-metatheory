{-# OPTIONS --without-K --rewriting #-}

module hott.NType where

open import hott.Base public

private
  variable {ℓ ℓ₁ ℓ₂ ℓ₃} : ULevel

ctr : {A : Type ℓ} (a : A) → ((x : A) → a == x) → is-contr A
ctr = curry has-level-in

module _ {A : Type ℓ} ⦃ w : is-prop A ⦄ (x y : A) where
  prop-paths-contr : is-contr (x == y)
  prop-paths-contr = has-level-in (has-level-apply (has-level-apply w x y))

  prop-paths-prop : is-prop (x == y)
  prop-paths-prop = contr-is-prop prop-paths-contr

prop-has-all-paths-idp :
  {A : Type ℓ} ⦃ w : is-prop A ⦄ (x : A)
  → prop-has-all-paths x x == idp
prop-has-all-paths-idp ⦃ w ⦄ x = prop-path (prop-paths-prop x x) _ _

module _ {A : Type ℓ₁} {n : ℕ₋₂} where
  -- Doubly indexed version of Π-level
  Π-level2 : {B : A → A → Type ℓ₂}
    → ((a a' : A) → has-level n (B a a')) → has-level n ((a a' : A) → B a a')
  Π-level2 h = Π-level (λ a → Π-level (λ a' → h a a'))

module _ {A : Type ℓ} ⦃ A-set : is-set A ⦄ {x y : A} where
  set-equality-is-prop : is-prop (x == y)
  set-equality-is-prop = has-level-apply-instance

  set-equality-has-all-paths : (p q : x == y) → p == q
  set-equality-has-all-paths = prop-path set-equality-is-prop
