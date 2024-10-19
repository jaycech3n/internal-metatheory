\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories

module categories.Semipullbacks {ℓₒ ℓₘ} (𝒞 : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory 𝒞 renaming (ass to α)

open import categories.CommutingSquares 𝒞

\end{code}

Recall that if 𝔓 is a commuting square on cospan c with vertex P, we have the
precomposition map
  𝔓 □[ X ]_ : hom X P → CommSq c X
for every X : Ob C. Then 𝔓 is a pullback if for each X this map has contractible
fibers, and a weak pullback if it has pointed (inhabited) fibers.

Here, say that 𝔓 is a *semipullback* if this map has *fst-contracted*
fibers, i.e. if (𝔓 □[ X ]_) is a family of fst-contracted maps.

\begin{code}

is-semi-pb : (c : Cospan) (P : Ob) → CommSq c P → Type (ℓₒ ∪ ℓₘ)
is-semi-pb c P 𝔓 = (X : Ob) → fst-contr (𝔓 □[ X ]_)

semi-pb-UP : (c : Cospan) (P : Ob) → CommSq c P → Type (ℓₒ ∪ ℓₘ)
semi-pb-UP c P 𝔓 =
  (X : Ob) (𝔖 : CommSq c X)
  → Σ[ m ﹕ hom X P ] Σ[ e ﹕ CommSqEq (𝔓 □ m) 𝔖 ]
     ((m' : hom X P) → CommSqEq (𝔓 □ m') 𝔖 → m' == m)

\end{code}
