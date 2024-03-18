Pullbacks in wild semicategories
================================

We work in a wild semicategory 𝒞.

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories

module categories.Pullbacks {ℓₒ ℓₘ} (𝒞 : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory 𝒞

\end{code}

Consider the type of commutative squares in 𝒞 with source tl on a cospan
csp :=
            tr
            | r
            v
    bl ---> br
        b

\begin{code}

record CommSqOn (tl tr bl br : Ob) (r : hom tr br) (b : hom bl br)
  : Type (ℓₒ ∪ ℓₘ)
  where
  constructor commsquare
  field
    t : hom tl tr
    l : hom tl bl
    comm : r ◦ t == b ◦ l

\end{code}

For any two objects tl and tl', 𝒞(tl', tl) acts on commutative squares on csp by
precomposition.

\begin{code}

commsq-◦ :
  ∀ {tl tr bl br : Ob} {r : hom tr br} {b : hom bl br}
  → CommSqOn tl tr bl br r b
  → ∀ tl'
  → hom tl' tl
  → CommSqOn tl' tr bl br r b
commsq-◦ {r = r} {b} (commsquare t l comm) _ m =
  commsquare (t ◦ m) (l ◦ m) p
  where
  p : r ◦ t ◦ m == b ◦ l ◦ m
  p = ! ass ∙ ap (_◦ m) comm ∙ ass

\end{code}

A pullback on the cospan csp is then a commutative square with source tl, such
that the precomposition action for any tl' is an equivalence.

\begin{code}

module _ (tr bl br : Ob) (r : hom tr br) (b : hom bl br) where

  record Pullback : Type (ℓₒ ∪ ℓₘ)
    where
    constructor pullback
    field
      tl : Ob
      commsq : CommSqOn tl tr bl br r b
      up : ∀ tl' → is-equiv (commsq-◦ commsq tl')

\end{code}

We want the "pullback prism" lemma to hold.
