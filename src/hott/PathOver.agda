{-# OPTIONS --without-K --rewriting #-}

module hott.PathOver where

open import hott.Base public

↓-equal-paths : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
                  {x y : A} {u : B x } {v : B y} {p q : x == y}
                  (α : p == q)
                → u == v [ B ↓ p ]
                → u == v [ B ↓ q ]
↓-equal-paths idp q = q

private
  module reasoning {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} where

    infixl 40 ap↓2

    ap↓2 :
      ∀ {ℓ₃} {C : {a : A} → B a → Type ℓ₃}
        {x y : A} {f : B x → B y}
        (g : {b : B x} → C b → (C ∘ f) b)
        {b b' : B x} {p : b == b'}
        {c : C b} {c' : C b'}
      → c == c' [ C ↓ p ]
      → g c == g c' [ C ↓ ap f p ]
    ap↓2 g {p = idp} q = ap g q

    syntax ap↓2 g q = q |in-ctx↓ g

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

open reasoning public
