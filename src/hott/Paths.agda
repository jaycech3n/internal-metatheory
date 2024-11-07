{-# OPTIONS --without-K --rewriting #-}

module hott.Paths where

open import hott.Base public

private
  variable ℓ ℓ₁ ℓ₂ ℓ₃ : ULevel

transp! : {A : Type ℓ₁} (B : A → Type ℓ₂)
  {x y : A} (p : x == y) → B y → B x
transp! B p = transp B (! p)

transp-∘ : {A : Type ℓ₁} {B : Type ℓ₂}
  (P : B → Type ℓ₃) (f : A → B)
  {x y : A} (p : x == y)
  → transp (P ∘ f) p == transp P (ap f p)
transp-∘ P f idp = idp

transp-transp! :
  {A : Type ℓ} (B : A → Type ℓ₂) {x y : A} (p : x == y) (b : B y)
  → transp B p (transp! B p b) == b
transp-transp! B idp b = idp

transp!-transp :
  {A : Type ℓ} (B : A → Type ℓ₂) {x y : A} (p : x == y) (b : B x)
  → transp! B p (transp B p b) == b
transp!-transp B idp b = idp

-- Basic facts about some basic definitions in HoTT-Agda

-- transport! is defined as (coe! ∘ ap)
transp!=transport! :
  {A : Type ℓ₁} {B : A → Type ℓ₂} {x y : A} (p : x == y) {b : B y}
  → transp! B p b == transport! B p b
transp!=transport! idp = idp

-- Compare coe!-inv-r in PathFunctor.agda from HoTT-Agda
coe-!-inv-r : ∀ {i} {A B : Type i} (p : A == B) (b : B)
  → coe p (coe (! p) b) == b
coe-!-inv-r idp b = idp

coe-!-inv-l : ∀ {i} {A B : Type i} (p : A == B) (a : A)
  → coe (! p) (coe p a) == a
coe-!-inv-l idp a = idp

coe-inv-adj' : ∀ {i} {A B : Type i} (p : A == B) (a : A) →
  ap (coe p) (coe-!-inv-l p a) == coe-!-inv-r p (coe p a)
coe-inv-adj' idp a = idp

coe-!-inv-adj : ∀ {i} {A B : Type i} (p : A == B) (b : B) →
  ap (coe (! p)) (coe-!-inv-r p b) == coe-!-inv-l p (coe (! p) b)
coe-!-inv-adj idp b = idp

-- Equivalence
transp-family-precomp-equiv :
  ∀ {ℓ₁ ℓ₂} {A B : Type ℓ₁} (e : A ≃ B)
  → {C : A → Type ℓ₂} (b : B) (c : C (<– e b))
  → transp! C (<–-inv-l e (<– e b)) c == transp! (C ∘ <– e) (<–-inv-r e b) c
transp-family-precomp-equiv {ℓ₁} {ℓ₂} = equiv-induction P d
  where
  P : {A B : Type ℓ₁} (e : A ≃ B) → Type _
  P {A = A} {B} e =
    {C : A → Type ℓ₂} (b : B) (c : C (<– e b))
    → transp! C (<–-inv-l e (<– e b)) c == transp! (C ∘ <– e) (<–-inv-r e b) c

  d : (A : Type ℓ₁) → P (ide A)
  d A b c = idp

transp-is-equiv :
  {A : Type ℓ₁} (B : A → Type ℓ₂) {x y : A} (p : x == y)
  → is-equiv (transp B p)
transp-is-equiv B p =
  is-eq _ (transp! B p) (transp-transp! B p) (transp!-transp B p)

-- Version of coe-equiv that doesn't use coe!
coe-equiv' : {A B : Type ℓ} → A == B → A ≃ B
coe-equiv' p =
  (coe p
  , record { g = coe (! p) ; f-g = coe-!-inv-r p ; g-f = coe-!-inv-l p
           ; adj = coe-inv-adj' p })

-- Version of transport-equiv with explicit maps
transp-equiv : {A : Type ℓ₁} (B : A → Type ℓ₂) {x y : A} → x == y → B x ≃ B y
transp-equiv B p = transp B p
  , is-eq _ (transp! B p) (transp-transp! B p) (transp!-transp B p)

-- Ad hoc lemmas used in various places
<!∙>∙!∙ : {A : Type ℓ} {x y z : A} (p : y == x) (q : y == z)
          → (! p ∙ q) ∙ ! q ∙ p == idp
<!∙>∙!∙ idp idp = idp

from-over-lr : {A : Type ℓ₁} (B : A → Type ℓ₂)
  → {x y z w : A} {u : B x} {v : B w}
  → (p : x == y) (q : y == z) (r : z == w)
  → u == v [ B ↓ p ∙ q ∙ r ]
  → transp B p u == transp! B r v [ B ↓ q ]
from-over-lr B idp idp idp p = p

ap-const :
  {A : Type ℓ₁} {B : Type ℓ₂} {b : B} {x y : A} (p : x == y)
  → ap (λ _ → b) p == idp
ap-const idp = idp
