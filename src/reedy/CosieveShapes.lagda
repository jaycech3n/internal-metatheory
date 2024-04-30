Shapes of cosieves in countably simple semicategories
=====================================================

In order to construct type theoretic inverse diagrams, we use a presentation of
linear cosieves in countably simple semicategories in terms of their "shapes".

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.CosieveShapes {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I


is-shape : ℕ → ℕ → ℕ → Type₀
is-shape i h t = t ≤ hom-size i h

\end{code}

Repeatedly used:

\begin{code}

prev-shape : ∀ {i h t} → is-shape i h (1+ t) → is-shape i h t
prev-shape = S≤-≤

full-shape : ∀ i h → is-shape i h (hom-size i h)
full-shape i h = lteE

total-shape-1+ : ∀ i → is-shape (1+ i) i (hom-size (1+ i) i)
total-shape-1+ i = full-shape (1+ i) i

empty-shape : ∀ i h → is-shape i h O
empty-shape i h = O≤ _

<-to-is-shape : ∀ {i h t} → t < hom-size i h → is-shape i h t
<-to-is-shape = inr

<-from-is-shape : ∀ {i h t} → is-shape i h (1+ t) → t < hom-size i h
<-from-is-shape = S≤-<

\end{code}

Being a shape is property:

\begin{code}

is-shape-is-prop : ∀ {i h t} → is-prop (is-shape i h t)
is-shape-is-prop = ≤-is-prop

is-shape-path : ∀ {i h t} (s s' : is-shape i h t) → s == s'
is-shape-path = prop-has-all-paths

instance
  is-shape-id-is-prop : ∀ {i h t} {s s' : is-shape i h t} → is-prop (s == s')
  is-shape-id-is-prop = =-preserves-level is-shape-is-prop

\end{code}


The type of shapes
------------------

\begin{code}

record Shape : Type₀ where
  eta-equality
  constructor shape
  field
    𝑖 : ℕ
    ℎ : ℕ
    𝑡 : ℕ
    Shape-is-shape : is-shape 𝑖 ℎ 𝑡

open Shape public

-- data Shape : Type₀ where
--   shape : (i h t : ℕ) (s : is-shape i h t) → Shape

\end{code}


Old formulation of the above:

Shape = Σ[ i ﹕ ℕ ] Σ[ h ﹕ ℕ ] Σ[ t ﹕ ℕ ] is-shape i h t

𝑖 : Shape → ℕ
𝑖 = fst

ℎ : Shape → ℕ
ℎ = fst ∘ snd

𝑡 : Shape → ℕ
𝑡 = 2nd ∘ snd

Shape-is-shape : ((i , h , t , _) : Shape) → is-shape i h t
Shape-is-shape = 3rd ∘ snd
