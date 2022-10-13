{-# OPTIONS --without-K #-}

module hott.Paths where

open import hott.Base public

transp! : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (B : A → Type ℓ₂) {x y : A} (p : x == y) → B y → B x
transp! B p = transp B (! p)

-- Ad hoc lemmas used in various places
<!∙>∙!∙ : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : y == x) (q : y == z)
          → (! p ∙ q) ∙ ! q ∙ p == idp
<!∙>∙!∙ idp idp = idp

