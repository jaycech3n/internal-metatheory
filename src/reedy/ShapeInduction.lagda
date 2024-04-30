Induction on shapes
===================

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.ShapeInduction {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open import hott.Induction
open import reedy.CosieveShapes I

open SimpleSemicategory I

\end{code}

Lexicographic order on shapes.

\begin{code}

data _>ₛ_ (sh : Shape) : Shape → Type₀ where
  on-𝑖 : ∀ {sh'} → 𝑖 sh > 𝑖 sh' → sh >ₛ sh'
  on-ℎ : ∀ {sh'} → 𝑖 sh == 𝑖 sh' → ℎ sh > ℎ sh' → sh >ₛ sh'
  on-𝑡 : ∀ {sh'} → 𝑖 sh == 𝑖 sh' → ℎ sh == ℎ sh' → 𝑡 sh > 𝑡 sh' → sh >ₛ sh'

_<ₛ_ : Shape → Shape → Type₀
sh <ₛ sh' = sh' >ₛ sh

-- shape-ind :

\end{code}
