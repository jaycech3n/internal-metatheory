{-# OPTIONS --without-K #-}

module hott.Paths where

open import hott.Base public

private
  variable ℓ : ULevel

-- Ad hoc lemmas used in various places
<!∙>∙!∙ : {A : Type ℓ} {x y z : A} (p : y == x) (q : y == z)
          → (! p ∙ q) ∙ ! q ∙ p == idp
<!∙>∙!∙ idp idp = idp

