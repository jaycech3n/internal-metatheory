{--- Not currently used -}

{-# OPTIONS --without-K --rewriting #-}

module hott.PathOverSeq where

open import hott.PathOver

data PathOverSeq {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
  : (x y : A) (u : B x) (v : B y) → Type (lsuc (ℓ₁ ∪ ℓ₂)) where
  _◾  : {x y : A} {p : x == y} {u : B x} {v : B y}
        → (u == v [ B ↓ p ]) → PathOverSeq x y u v
  _▸_ : {x y z : A} {p : x == y} {u : B x} {v : B y} {w : B z}
        → (u == v [ B ↓ p ]) → PathOverSeq y z v w → PathOverSeq x z u w

infix 11 _◾
infixr 10 _▸_

base-path :
  ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} {u : B x} {v : B y}
  → PathOverSeq x y u v
  → x == y
base-path (_◾ {p = p} _) = p
base-path (_▸_ {p = p} _ s) = p ∙ base-path s

to-PathOver :
  ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} {u : B x} {v : B y}
  → (s : PathOverSeq x y u v)
  → PathOver B (base-path s) u v
to-PathOver (q ◾) = q
to-PathOver (q ▸ s) = q ∙ᵈ to-PathOver s

private
  module notation where
    PathOverSeq-syntax :
      ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
      (x y : A) (u : B x) (v : B y) → ⊤ → Type (lsuc (ℓ₁ ∪ ℓ₂))
    PathOverSeq-syntax x y u v _ = PathOverSeq x y u v
    syntax PathOverSeq-syntax x y u v t = u === v ↓ t ↓ x === y

open notation public
