Commuting squares in wild semicategories
========================================

We work in a wild semicategory 𝒞.

\begin{code}

{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import categories.Semicategories

module categories.CommutingSquares {ℓₒ ℓₘ} (𝒞 : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory 𝒞 renaming (ass to α)

\end{code}

Cospans and commuting squares

          mB
       X ---> B
    mA | ↗ p  | g
       ↓      ↓
       A ---> C
          f

\begin{code}

record Cospan : Type (ℓₒ ∪ ℓₘ) where
  constructor cospan
  field
    {A B C} : Ob
    f : hom A C
    g : hom B C

record CommSq (c : Cospan) (X : Ob) : Type (ℓₒ ∪ ℓₘ) where
  constructor square

  A = Cospan.A c
  B = Cospan.B c
  f = Cospan.f c
  g = Cospan.g c

  field
    mA : hom X A
    mB : hom X B
    γ : f ◦ mA == g ◦ mB

\end{code}

Equality of commuting squares. The following is actually a characterization
(proof left to later).

\begin{code}

module _ {c : Cospan} {X : Ob} where
  open CommSq

  CommSqEq : (𝔖 𝔖' : CommSq c X) → Type _
  CommSqEq 𝔖 𝔖' =
    Σ[ eA ﹕ mA 𝔖 == mA 𝔖' ]
    Σ[ eB ﹕ mB 𝔖 == mB 𝔖' ]
    (γ 𝔖 == (Cospan.f c ∗ₗ eA) ∙ γ 𝔖' ∙ ! (Cospan.g c ∗ₗ eB))

  square= : ∀ 𝔖 𝔖' → CommSqEq 𝔖 𝔖' → 𝔖 == 𝔖'
  square= = {!!}

  CommSqEq≃CommSq-equality : ∀ 𝔖 𝔖' → CommSqEq 𝔖 𝔖' ≃ (𝔖 == 𝔖')
  CommSqEq≃CommSq-equality = {!!}

\end{code}

Vertical pasting of commuting squares

           i
       A' ---> A
    f' |  ↗ q  | f
       ↓   j   ↓
       B' ---> B
    g' |  ↗ p  | g
       ↓       ↓
       C' ---> C
           k

\begin{code}

sqvpaste :
  {C' C B : Ob} {k : hom C' C} {g : hom B C} {B' : Ob}
  (𝔓 : CommSq (cospan k g) B')
  {A : Ob} {f : hom A B} {A' : Ob}
  (𝔔 : CommSq (cospan (CommSq.mB 𝔓) f) A')
  → CommSq (cospan k (g ◦ f)) A'
sqvpaste {g = g} 𝔓 𝔔 =
  square (mA 𝔓 ◦ mA 𝔔) (mB 𝔔) $
  ! α ∙ (γ 𝔓 ∗ᵣ mA 𝔔) ∙ α ∙ (g ∗ₗ γ 𝔔) ∙ ! α
  where open CommSq hiding (g)

\end{code}

Precomposition of squares with morphisms

\begin{code}

infixl 70 _□_ _□[_]_

_□_ : {c : Cospan} {X Y : Ob} → CommSq c Y → hom X Y → CommSq c X
square mA mB γ □ m = square (mA ◦ m) (mB ◦ m) (! α ∙ (γ ∗ᵣ m) ∙ α)

_□[_]_ : {c : Cospan} {Y : Ob} → CommSq c Y → (X : Ob) → hom X Y → CommSq c X
𝔓 □[ X ] m = 𝔓 □ m

\end{code}

