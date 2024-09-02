{-# OPTIONS --without-K --rewriting #-}

module hott.IdentitySystems where

open import hott.Base public
open import hott.Sigma public
open import hott.NType public
open import hott.Universes public

-- Based identity systems on a fixed universe 𝒰.
record is-IdS {𝒰} {A : 𝒰 ̇ } (a₀ : A) (R : A → 𝒰 ̇ ) (r₀ : R a₀) : 𝒰 ⁺ ̇
  where
  constructor IdS
  field
    IdSJ  : (P : (x : A) → R x → 𝒰 ̇ ) → P a₀ r₀ → ∀ x r → P x r
    IdSJβ : {P : (x : A) → R x → 𝒰 ̇ } (p₀ : P a₀ r₀) → IdSJ P p₀ a₀ r₀ == p₀

  from-= : ∀ x → a₀ == x → R x
  from-= .a₀ idp = r₀

  to-= : ∀ x → R x → a₀ == x
  to-= = IdSJ (λ x _ → a₀ == x) idp

  to-=-ise : ∀ x → is-equiv (to-= x)
  to-=-ise x = is-eq _ (from-= x) to-from (from-to x)
    where
    to-from : to-= x ∘ from-= x ∼ idf _
    to-from idp = IdSJβ idp

    from-to : ∀ x (r : R x) → from-= x (to-= x r) == r
    from-to = IdSJ _ (ap (from-= a₀) (IdSJβ idp))

  fiberwise-= : ∀ x → R x ≃ (a₀ == x)
  fiberwise-= x = to-= x , to-=-ise x

  total-space-is-contr : is-contr (Σ A R)
  total-space-is-contr =
    -- Direct proof using J of the identity system R
    ctr (a₀ , r₀) (uncurry $ IdSJ _ idp)
    -- Alternatively, by fiberwise equivalence of R with a₀ ==_,
    -- pathfrom-is-contr a₀ ◂$ transp! is-contr (ua (Σ-emap-r fiberwise-=))

open is-IdS

-- Being an identity system is a proposition on pointed predicates (R, r₀)
is-IdS-is-prop :
  ∀ {𝒰} {A : 𝒰 ̇ } (a₀ : A) (R : A → 𝒰 ̇ ) (r₀ : R a₀)
  → is-prop (is-IdS a₀ R r₀)
is-IdS-is-prop {𝒰} {A} a₀ R r₀ = transp is-prop (ua aux) thus
  where
  -- Represent is-IdS as a Σ-type
  is-IdS-Σ-rep : 𝒰 ⁺ ̇
  is-IdS-Σ-rep =
    Σ ((P : (x : A) → R x → 𝒰 ̇ ) → P a₀ r₀ → ∀ x r → P x r)
    λ J → (P : (x : A) → R x → 𝒰 ̇ ) (p₀ : P a₀ r₀) → J P p₀ a₀ r₀ == p₀

  aux : is-IdS-Σ-rep ≃ is-IdS a₀ R r₀
  fst aux (J , Jβ) = IdS J (λ {P} → Jβ P)
  snd aux = is-eq _
    (λ{ (IdS IdSJ IdSJβ) → IdSJ , λ P → IdSJβ {P}})
    (λ _ → idp) (λ _ → idp)

  -- Two applications of type theoretic AC
  calc :
    is-IdS-Σ-rep
    == ( (P : (x : A) → R x → 𝒰 ̇ ) (p : P a₀ r₀)
       → Σ[ J ﹕ ((x : A) (y : R x) → P x y) ] J a₀ r₀ == p )
  calc =
    is-IdS-Σ-rep
    =⟨ ua $ choice ⁻¹ ⟩
    ( (P : (x : A) → R x → 𝒰 ̇ )
    → Σ[ J ﹕ ((p : P a₀ r₀) (x : A) (y : R x) → P x y) ]
       ((p : P a₀ r₀) → J p a₀ r₀ == p) )
    =⟨ {!!} ⟩
    ( (P : (x : A) → R x → 𝒰 ̇ )
      (p : P a₀ r₀)
    → Σ[ J ﹕ ((x : A) (y : R x) → P x y) ] J a₀ r₀ == p)
    =∎

  have : is-contr is-IdS-Σ-rep
  have = {!!} -- the Σ in the RHS of calc is equivalent to a singleton

  thus : is-prop is-IdS-Σ-rep
  thus = {!!}

-- Thus because every pointed predicate (R, r₀) on (A, a₀) is equal to the
-- canonical pointed predicate (λ x → a₀ == x, idp), the type of based identity
-- systems on (A, a₀) is contractible.
