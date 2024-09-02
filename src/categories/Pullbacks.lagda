Pullbacks in wild semicategories
================================

\begin{code}

{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import categories.Semicategories

module categories.Pullbacks {ℓₒ ℓₘ} (𝒞 : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory 𝒞 renaming (ass to α)

open import categories.CommutingSquares 𝒞

\end{code}

Weak pullbacks

\begin{code}

is-weak-pb : (c : Cospan) (P : Ob) → CommSq c P → Type _
is-weak-pb c P 𝔓 = (X : Ob) → is-retraction (𝔓 □[ X ]_)

\end{code}

By the characterization of equality of commuting squares, get the equivalent
universal property:

\begin{code}

weak-pb-UP : (c : Cospan) (P : Ob) → CommSq c P → Type _
weak-pb-UP c P (square πA πB 𝔭) =
  (X : Ob) (𝔖@(square mA mB γ) : CommSq c X)
  → Σ[ m ﹕ hom X P ]
    Σ[ eA ﹕ πA ◦ m == mA ]
    Σ[ eB ﹕ πB ◦ m == mB ]
    ! α ∙ (𝔭 ∗ᵣ m) ∙ α == (Cospan.f c ∗ₗ eA) ∙ γ ∙ ! (Cospan.g c ∗ₗ eB)

\end{code}

Pullbacks

\begin{code}

is-pb : (c : Cospan) (P : Ob) → CommSq c P → Type _
is-pb c P 𝔓 = (X : Ob) → is-equiv (𝔓 □[ X ]_)

\end{code}

By the contractible fibers definition of equivalences, get the universal
property:

\begin{code}

pb-UP : (c : Cospan) (P : Ob) → CommSq c P → Type _
pb-UP c P 𝔓 =
  (X : Ob) (𝔖@(square mA mB γ) : CommSq c X)
  → is-contr (weak-pb-UP c P 𝔓)

pb-properties-equiv : ∀ c P 𝔓 → pb-UP c P 𝔓 ≃ is-pb c P 𝔓
pb-properties-equiv c P 𝔓 = {!!}

pb-UP-is-pb : ∀ c P 𝔓 → pb-UP c P 𝔓 → is-pb c P 𝔓
pb-UP-is-pb c p 𝔓 = –> $ pb-properties-equiv c p 𝔓

\end{code}

Semi-pullbacks; an intermediate notion of pullback.

\begin{code}

-- semi-pb-UP :

\end{code}
