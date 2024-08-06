{-# OPTIONS --without-K --rewriting #-}

module hott.IdentitySystems where

open import hott.Sigma public
open import hott.Universes public

-- Based identity systems on a fixed universe 𝒰.
record is-identity-system {𝒰} {A : 𝒰 ̇ } (a₀ : A) (R : A → 𝒰 ̇ ) (r₀ : R a₀) : 𝒰 ⁺ ̇
  where
  constructor IdS
  field
    IdSJ  : (P : (x : A) → R x → 𝒰 ̇ ) → P a₀ r₀ → ∀ x r → P x r
    IdSJβ : {P : (x : A) → R x → 𝒰 ̇ } (p₀ : P a₀ r₀) → IdSJ P p₀ a₀ r₀ == p₀

  from-= : ∀ x → a₀ == x → R x
  from-= .a₀ idp = r₀

  to-= : ∀ x → R x → a₀ == x
  to-= = IdSJ (λ x _ → a₀ == x) idp

  -- to-= and from-= are inverse equivalences
  to-=-is-equiv : ∀ x → is-equiv (to-= x)
  to-=-is-equiv x = is-eq _ (from-= x) to-from (from-to x)
    where
    to-from : to-= x ∘ from-= x ∼ idf _
    to-from idp = IdSJβ idp

    from-to : ∀ x (r : R x) → from-= x (to-= x r) == r
    from-to = IdSJ _ (ap (from-= a₀) (IdSJβ idp))

  fiberwise-= : ∀ x → R x ≃ (a₀ == x)
  fiberwise-= x = to-= x , to-=-is-equiv x

  total-space-is-contr : is-contr (Σ A R)
  total-space-is-contr = has-level-in
    ( (a₀ , r₀)
    , uncurry (IdSJ _ idp) )

open is-identity-system

is-identity-system' :
  ∀ {𝒰} {A : 𝒰 ̇ } (a₀ : A) (R : A → 𝒰 ̇ ) (r₀ : R a₀) → 𝒰 ⁺ ̇
is-identity-system' {𝒰} {A} a₀ R r₀ =
  Σ[ IdSJ ﹕ ((P : (x : A) → R x → 𝒰 ̇ ) → P a₀ r₀ → ∀ x r → P x r) ]
   ( (P : (x : A) → R x → 𝒰 ̇ ) (p₀ : P a₀ r₀) → IdSJ P p₀ a₀ r₀ == p₀ )

-- Here we try to directly show that being an identity system is equivalent to
-- having contractible total space.
module _ {𝒰} {A : 𝒰 ̇ } (a₀ : A) (R : A → 𝒰 ̇ ) (r₀ : R a₀) where
  is-id-sys-total-space-is-contr :
    is-identity-system a₀ R r₀ → is-contr (Σ A R)
  is-id-sys-total-space-is-contr is-ids = total-space-is-contr is-ids

  total-space-is-contr-is-id-sys :
    is-contr (Σ A R) → is-identity-system a₀ R r₀
  IdSJ (total-space-is-contr-is-id-sys ΣAR-is-contr) P p₀ a r =
    transp (uncurry P) path p₀
    where
    ΣAR-is-prop = contr-is-prop ΣAR-is-contr
    path = prop-path ΣAR-is-prop (a₀ , r₀) (a , r)
  IdSJβ (total-space-is-contr-is-id-sys ΣAR-is-contr) {P} p₀ =
    ap (λ path → transp (uncurry P) path p₀)
       (prop-path (raise-level _ $ =-preserves-contr ΣAR-is-contr) _ idp)
    where
    ΣAR-is-prop = contr-is-prop ΣAR-is-contr
    path = prop-path ΣAR-is-prop (a₀ , r₀) (a₀ , r₀)
    -- test = =-preserves-level {x = path} {idp} (=-preserves-contr ΣAR-is-contr)

  lem : is-identity-system a₀ R r₀ ≃ is-contr (Σ A R)
  lem =
    is-id-sys-total-space-is-contr ,
    is-eq _ total-space-is-contr-is-id-sys f-g g-f
    where
    f-g = λ contr → prop-path is-contr-is-prop _ contr
    g-f = λ is-ids → {!!}
