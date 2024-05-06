{-# OPTIONS --without-K --rewriting #-}

module hott.PathOver where

open import hott.Base public

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} where

  to-transp' :
    {a a' : A} {p : a == a'}
    {u : B a} {v : B a'}
    → (u == v [ B ↓ p ])
    → u == transp B (! p) v
  to-transp' {p = idp} idp = idp

  ↓-equal-paths :
    {x y : A} {u : B x } {v : B y} {p q : x == y}
    (α : p == q)
    → u == v [ B ↓ p ]
    → u == v [ B ↓ q ]
  ↓-equal-paths idp q = q

  -- A variation of ap↓
  ap↓2 :
    ∀ {ℓ₃} {C : Type ℓ₃}
      (f : (a : A) → B a → C)
      {a a' : A} {b : B a} {b' : B a'}
    → (p : a == a')
    → (q : b == b' [ B ↓ p ])
    → f a b == f a' b'
  ap↓2 f {a} idp q = ap (f a) q

  infixl 40 ap↓² ap↓³
  ap↓² :
    ∀ {ℓ₃} {C : {a : A} → B a → Type ℓ₃}
      {x y : A} {f : B x → B y}
      (g : {b : B x} → C b → C (f b))
      {b b' : B x} {p : b == b'}
      {c : C b} {c' : C b'}
    → c == c' [ C ↓ p ]
    → g c == g c' [ C ↓ ap f p ]
  ap↓² g {p = idp} q = ap g q

  syntax ap↓² g q = q |in-ctx↓ g

  ap↓³ : ∀ {ℓ₃ ℓ₄}
    {C : {a : A} → B a → Type ℓ₃}
    {D : {a : A} {b : B a} → C b → Type ℓ₄}
    {a a' : A} {b : B a} {b' : B a'}
    {f : C b → C b'}
    (g : {c : C b} → D c → D (f c))
    {c c' : C b} {p : c == c'}
    {d : D c} {d' : D c'}
    → d == d' [ D ↓ p ]
    → g d == g d' [ D ↓ ap f p ]
  ap↓³ g {p = idp} q = ap g q

  -- =⟨_⟩ notation
  infix 12 =⟨⟩ᵈ =⟨!⟩ᵈ =⟨↓⟩ᵈ
  infixr 11 =⟨⟩ᵈ-compr =⟨!⟩ᵈ-compr =⟨↓⟩ᵈ-compr
  infixl 11 =⟨⟩ᵈ-compl =⟨!⟩ᵈ-compl =⟨↓⟩ᵈ-compl

  =⟨⟩ᵈ : {a a' : A} {p : a == a'}
         (b : B a) (b' : B a') (q : b == b' [ B ↓ p ])
         → b == b' [ B ↓ p ]
  =⟨⟩ᵈ _ _ q = q

  =⟨!⟩ᵈ : {a a' : A} {p : a == a'}
          (b : B a) (b' : B a') (q : b == b' [ B ↓ p ])
          → b' == b [ B ↓ ! p ]
  =⟨!⟩ᵈ _ _ q = !ᵈ q

  =⟨⟩ᵈ-compr :
    {a a' a'' : A} {p : a == a'} {p' : a' == a''}
    (b : B a) {b' : B a'} {b'' : B a''}
    → b == b' [ B ↓ p ]
    → b' == b'' [ B ↓ p' ]
    → b == b'' [ B ↓ p ∙ p' ]
  =⟨⟩ᵈ-compr _ q q' = q ∙ᵈ q'

  =⟨!⟩ᵈ-compr :
    {a a' a'' : A} {p : a' == a} {p' : a' == a''}
    (b : B a) {b' : B a'} {b'' : B a''}
    → b' == b [ B ↓ p ]
    → b' == b'' [ B ↓ p' ]
    → b == b'' [ B ↓ ! p ∙ p' ]
  =⟨!⟩ᵈ-compr _ q q' = !ᵈ q ∙ᵈ q'

  =⟨⟩ᵈ-compl :
    {a a' a'' : A} {p : a == a'} {p' : a' == a''}
    {b : B a} {b' : B a'} (b'' : B a'')
    → b == b' [ B ↓ p ]
    → b' == b'' [ B ↓ p' ]
    → b == b'' [ B ↓ p ∙ p' ]
  =⟨⟩ᵈ-compl _ q q' = q ∙ᵈ q'

  =⟨!⟩ᵈ-compl :
    {a a' a'' : A} {p : a == a'} {p' : a'' == a'}
    {b : B a} {b' : B a'} (b'' : B a'')
    → b == b' [ B ↓ p ]
    → b'' == b' [ B ↓ p' ]
    → b == b'' [ B ↓ p ∙ ! p' ]
  =⟨!⟩ᵈ-compl _ q q' = q ∙ᵈ !ᵈ q'

  syntax =⟨⟩ᵈ b b' q = b =⟨ q ⟩ᵈ b'
  syntax =⟨⟩ᵈ-compr b q q' = b =⟨ q ⟫ᵈ q'
  syntax =⟨⟩ᵈ-compl b'' q q' = q =⟪ q' ⟩ᵈ b''
  syntax =⟨!⟩ᵈ b b' q = b =⟨! q ⟩ᵈ b'
  syntax =⟨!⟩ᵈ-compr b q q' = b =⟨! q ⟫ᵈ q'
  syntax =⟨!⟩ᵈ-compl b q q' = q =⟪! q' ⟩ᵈ b

  =⟨↓⟩ᵈ = =⟨⟩ᵈ
  =⟨↓⟩ᵈ-compr = =⟨⟩ᵈ-compr
  =⟨↓⟩ᵈ-compl = =⟨⟩ᵈ-compl

  syntax =⟨↓⟩ᵈ {p = p} b b' q = b =⟨ q ↓ p ⟩ᵈ b'
  syntax =⟨↓⟩ᵈ-compr {p = p} b q q' = b =⟨ q ↓ p ⟫ᵈ q'
  syntax =⟨↓⟩ᵈ-compl {p' = p'} b'' q q' = q =⟪ q' ↓ p' ⟩ᵈ b''

  infix 1 _=∎ᵈ _=∎↓⟨_⟩

  _=∎ᵈ : {a a' : A} {p : a == a'} {b : B a} {b' : B a'}
         → b == b' [ B ↓ p ] → b == b' [ B ↓ p ]
  q =∎ᵈ = q

  _=∎↓⟨_⟩ : {a a' : A} {p : a == a'} {q : a == a'} {b : B a} {b' : B a'}
       → b == b' [ B ↓ p ] → p == q → b == b' [ B ↓ q ]
  dp =∎↓⟨ α ⟩ = ↓-equal-paths α dp
