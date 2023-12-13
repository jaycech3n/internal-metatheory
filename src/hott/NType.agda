{-# OPTIONS --without-K --rewriting #-}

module hott.NType where

open import hott.Base public

private
  variable {ℓ ℓ₁ ℓ₂ ℓ₃} : ULevel

module _ {A : Type ℓ} ⦃ w : is-prop A ⦄ (x y : A) where
  prop-paths-contr : is-contr (x == y)
  prop-paths-contr = has-level-in (has-level-apply (has-level-apply w x y))

  prop-paths-prop : is-prop (x == y)
  prop-paths-prop = contr-is-prop prop-paths-contr

prop-has-all-paths-idp : {A : Type ℓ} ⦃ w : is-prop A ⦄ (x : A)
                         → prop-has-all-paths x x == idp
prop-has-all-paths-idp ⦃ w ⦄ x = prop-path (prop-paths-prop x x) _ _
