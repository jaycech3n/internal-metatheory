Commuting squares in wild semicategories
========================================

We work in a wild semicategory 𝒞.

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories
  renaming (Cospan to TypeCospan)

module categories.CommutingSquares {ℓₒ ℓₘ} (𝒞 : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory 𝒞
  renaming (ass to α)

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

Equality of commuting squares

\begin{code}

module _ {c : Cospan} {X : Ob} (𝔖 𝔖' : CommSq c X) where
  open CommSq
  square= :
    (eA : mA 𝔖 == mA 𝔖')
    (eB : mB 𝔖 == mB 𝔖')
    → γ 𝔖 == (Cospan.f c ∗ₗ eA) ∙ γ 𝔖' ∙ ! (Cospan.g c ∗ₗ eB)
    → 𝔖 == 𝔖'
  square= = {!!}

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

vpaste :
  {C' C B : Ob} {k : hom C' C} {g : hom B C} {B' : Ob}
  (𝔓 : CommSq (cospan k g) B')
  {A : Ob} {f : hom A B} {A' : Ob}
  (𝔔 : CommSq (cospan (CommSq.mB 𝔓) f) A')
  → CommSq (cospan k (g ◦ f)) A'
vpaste {g = g} 𝔓 𝔔 =
  square (mA 𝔓 ◦ mA 𝔔) (mB 𝔔) $
  ! α ∙ (γ 𝔓 ∗ᵣ mA 𝔔) ∙ α ∙ (g ∗ₗ γ 𝔔) ∙ ! α
  where open CommSq hiding (g)

-- Explicitly give every component
vpaste' :
  {A' B' C' A B C : Ob}
  (i : hom A' A) (j : hom B' B) (k : hom C' C)
  (f' : hom A' B') (g' : hom B' C')
  (f : hom A B) (g : hom B C)
  (q : j ◦ f' == f ◦ i)
  (p : k ◦ g' == g ◦ j)
  → CommSq (cospan k (g ◦ f)) A'
vpaste' i j k f' g' f g q p =
  square (g' ◦ f') i $
  ! α ∙ (p ∗ᵣ f') ∙ α ∙ (g ∗ₗ q) ∙ ! α

\end{code}

Precomposition of squares with morphisms

\begin{code}

_□_ : {c : Cospan} {X Y : Ob} → CommSq c Y → hom X Y → CommSq c X
square mA mB γ □ m = square (mA ◦ m) (mB ◦ m) (! α ∙ (γ ∗ᵣ m) ∙ α)

\end{code}

\begin{code}

module scratch
  (A' B' C' A B C : Ob)
  (i : hom A' A) (j : hom B' B) (k : hom C' C)
  (f' : hom A' B') (g' : hom B' C')
  (f : hom A B) (g : hom B C)
  (q : j ◦ f' == f ◦ i)
  (p : k ◦ g' == g ◦ j)
  (X : Ob) (m : hom X A')
  where

  𝔔 = square f' i q
  𝔓 = square g' j p

  [𝔔/𝔓]□m = (vpaste 𝔓 𝔔) □ m
  𝔔□m/𝔓 = vpaste 𝔓 (𝔔 □ m)

  want : [𝔔/𝔓]□m == 𝔔□m/𝔓
  want = square= [𝔔/𝔓]□m 𝔔□m/𝔓 α idp ({!!} :> (lhs == rhs))
    where
    lhs = ! α ∙ ((! α ∙ (p ∗ᵣ f') ∙ α ∙ (g ∗ₗ q) ∙ ! α) ∗ᵣ m) ∙ α
    rhs = (k ∗ₗ α) ∙
      (! α ∙
       (p ∗ᵣ (f' ◦ m)) ∙ α ∙ ap (_◦_ g) (! α ∙ ap (_◦ m) q ∙ α) ∙ ! α) ∙ idp

\end{code}
