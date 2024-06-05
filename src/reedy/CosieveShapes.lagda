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

prev-is-shape : ∀ {i h t} → is-shape i h (1+ t) → is-shape i h t
prev-is-shape = S≤-≤

full-is-shape : ∀ i h → is-shape i h (hom-size i h)
full-is-shape i h = lteE

total-is-shape-1+ : ∀ i → is-shape (1+ i) i (hom-size (1+ i) i)
total-is-shape-1+ i = full-is-shape (1+ i) i

<-to-is-shape : ∀ {i h t} → t < hom-size i h → is-shape i h t
<-to-is-shape = inr

<-from-is-shape : ∀ {i h t} → is-shape i h (1+ t) → t < hom-size i h
<-from-is-shape = S≤-<

\end{code}

Equality of shape witnesses.

\begin{code}

is-shape-is-prop : ∀ {i h t} → is-prop (is-shape i h t)
is-shape-is-prop = ≤-is-prop

is-shape-path : ∀ {i h t} (s s' : is-shape i h t) → s == s'
is-shape-path = prop-has-all-paths

instance
  is-shape-id-is-prop : ∀ {i h t} {s s' : is-shape i h t} → is-prop (s == s')
  is-shape-id-is-prop = =-preserves-level is-shape-is-prop

is-shape=↓ :
  ∀ i h {t t'}
  → {s : is-shape i h t} {s' : is-shape i h t'}
  → (p : t == t')
  → s == s' [ is-shape i h ↓ p ]
is-shape=↓ i h idp = prop-path is-shape-is-prop _ _

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

prev-shape : ∀ {i h t} → is-shape i h (1+ t) → Shape
prev-shape {i} {h} {t} s = shape i h t (prev-is-shape s)

full-shape : ∀ i h → Shape
full-shape i h = shape i h (hom-size i h) (full-is-shape i h)

total-shape-1+ : ∀ i → Shape
total-shape-1+ i = full-shape (1+ i) i

total-shape : (i : ℕ) → Shape
total-shape O = shape O O O (O≤ _)
total-shape (1+ i) = total-shape-1+ i

Shape= :
  ∀ i h t {s} {s'}
  → shape i h t s == shape i h t s'
Shape= i h t = ap (shape i h t) $ is-shape-path _ _

shape=-𝑖= : {sh sh' : Shape} → sh == sh' → 𝑖 sh == 𝑖 sh'
shape=-𝑖= idp = idp

\end{code}


Bounded shapes
--------------

\begin{code}

[_]BoundedShape : (b : ℕ) → Type₀
[ b ]BoundedShape = Σ Shape λ sh → ℎ sh < b

prev-bshape : ∀ {b i h t}
  → is-shape i h (1+ t) → h < b → [ b ]BoundedShape
prev-bshape s u = prev-shape s , u

full-bshape : ∀ {b} i h → h < b → [ b ]BoundedShape
full-bshape {b} i h u = full-shape i h , u

\end{code}


Bundled version; not used.

--```
record BoundedShape : Type₀ where
  eta-equality
  constructor _፦_
  field
    𝑏 : ℕ
    𝑠ℎ𝑢 : [ 𝑏 ]BoundedShape

open BoundedShape public
--```
