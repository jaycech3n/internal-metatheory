Well founded orders on shapes
=============================

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.ShapeOrder {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open import hott.Induction
import reedy.CosieveShapes as Sh
open Sh I

open SimpleSemicategory I

\end{code}


Lexicographic order on shapes
-----------------------------

\begin{code}

data _>ₛ_ (sh : Shape) : Shape → Type₀ where
  on-𝑖 : ∀ {sh'} → 𝑖 sh > 𝑖 sh' → sh >ₛ sh'
  on-ℎ : ∀ {h' t' s'} → ℎ sh > h' → sh >ₛ shape (𝑖 sh) h' t' s'
  on-𝑡 : ∀ {t' s'} → 𝑡 sh > t' → sh >ₛ shape (𝑖 sh) (ℎ sh) t' s'

_<ₛ_ : Shape → Shape → Type₀
sh <ₛ sh' = sh' >ₛ sh

<ₛ-trans : ∀ {sh sh' sh''} → sh <ₛ sh' → sh' <ₛ sh'' → sh <ₛ sh''
<ₛ-trans (on-𝑖 u) (on-𝑖 v) = on-𝑖 (<-trans u v)
<ₛ-trans (on-𝑖 u) (on-ℎ _) = on-𝑖 u
<ₛ-trans (on-𝑖 u) (on-𝑡 _) = on-𝑖 u
<ₛ-trans (on-ℎ _) (on-𝑖 v) = on-𝑖 v
<ₛ-trans (on-ℎ u) (on-ℎ v) = on-ℎ (<-trans u v)
<ₛ-trans (on-ℎ u) (on-𝑡 _) = on-ℎ u
<ₛ-trans (on-𝑡 _) (on-𝑖 v) = on-𝑖 v
<ₛ-trans (on-𝑡 _) (on-ℎ v) = on-ℎ v
<ₛ-trans (on-𝑡 u) (on-𝑡 v) = on-𝑡 (<-trans u v)

_≤ₛ_ : Shape → Shape → Type₀
sh ≤ₛ sh' = (sh == sh') ⊔ (sh <ₛ sh')

≤ₛ-trans : ∀ {sh sh' sh''} → sh ≤ₛ sh' → sh' ≤ₛ sh'' → sh ≤ₛ sh''
≤ₛ-trans (inl idp) v = v
≤ₛ-trans (inr u) (inl idp) = inr u
≤ₛ-trans (inr u) (inr v) = inr (<ₛ-trans u v)

𝑖-≤ₛ : ∀ {sh sh'} → sh ≤ₛ sh' → 𝑖 sh ≤ 𝑖 sh'
𝑖-≤ₛ (inl idp) = lteE
𝑖-≤ₛ (inr (on-𝑖 w)) = inr w
𝑖-≤ₛ (inr (on-ℎ _)) = lteE
𝑖-≤ₛ (inr (on-𝑡 _)) = lteE

\end{code}

Need all the following for the recursion in the diagram construction.

\begin{code}

≤ₛ𝑡 : ∀ {i h t t' s s'} → t' ≤ t → shape i h t' s' ≤ₛ shape i h t s
≤ₛ𝑡 (inl idp) = inl (ap (shape _ _ _) (is-shape-path _ _))
≤ₛ𝑡 (inr u) = inr (on-𝑡 u)

<ₛS𝑡-≤ₛ𝑡 :
  ∀ {i h t s s'} sh
  → sh <ₛ shape i h (1+ t) s
  → sh ≤ₛ shape i h t s'
<ₛS𝑡-≤ₛ𝑡 sh (on-𝑖 w) = inr (on-𝑖 w)
<ₛS𝑡-≤ₛ𝑡 .(shape _ _ _ _) (on-ℎ w) = inr (on-ℎ w)
<ₛS𝑡-≤ₛ𝑡 .(shape _ _ _ _) (on-𝑡 w) = ≤ₛ𝑡 (<S-≤ w)

-- Could/should probably reformulate in terms of bounded shapes
<ₛ-improper₀-≤ₛ-full :
  ∀ sh i {s} → ℎ sh < 1 → sh <ₛ shape (1+ i) O O s → sh ≤ₛ full-shape i O
<ₛ-improper₀-≤ₛ-full (shape i₀ .O t₀ s₀) .i₀ ltS (on-𝑖 ltS) = ≤ₛ𝑡 s₀
<ₛ-improper₀-≤ₛ-full (shape i₀ h₀ t₀ s₀) i u (on-𝑖 (ltSR w)) = inr (on-𝑖 w)

\end{code}

Well foundedness of <ₛ.

\begin{code}

<ₛ-Acc = Acc Shape _<ₛ_

rec-of : ∀ {sh} → <ₛ-Acc sh → _
rec-of (acc _ rec) = rec

<ₛ-Accc : ∀ i h t s → Type₀
<ₛ-Accc i h t s = <ₛ-Acc (shape i h t s)

<ₛ-is-wf-aux : ∀ i h t s → <ₛ-Acc (shape i h t s)
<ₛ-is-wf-aux i h t s = acc _ (aux i h t s)
  where
  -- By case distinction on the proof of <ₛ
  aux : ∀ i h t s → ∀ sh' → sh' <ₛ shape i h t s → <ₛ-Acc sh'
  aux .(1+ i') h t s (shape i' h' t' s') (on-𝑖 ltS) = <ₛ-is-wf-aux i' h' t' s'
  aux (1+ i) h t s sh' (on-𝑖 (ltSR w)) = aux i O O (O≤ _) sh' (on-𝑖 w)
  aux i h t s (shape .i h' t' s') (on-ℎ ltS) = <ₛ-is-wf-aux i h' t' s'
  aux i (1+ h) t s sh' (on-ℎ (ltSR w)) = aux i h O (O≤ _) sh' (on-ℎ w)
                                         -- could also use (i, h, full)
  aux i h .(1+ _) s (shape i h t' s') (on-𝑡 ltS) = <ₛ-is-wf-aux i h t' s'
  aux i h (1+ t) s sh' (on-𝑡 (ltSR w)) = aux i h t (prev-is-shape s) sh' (on-𝑡 w)

<ₛ-is-wf : ∀ {sh} → <ₛ-Acc sh
<ₛ-is-wf {shape i h t s} = <ₛ-is-wf-aux i h t s


open WellFoundedInduction Shape _<ₛ_ (λ sh → <ₛ-is-wf {sh})
  renaming (wf-ind to shape-ind)
  public

<ₛ-Acc-is-prop : ∀ sh → is-prop (<ₛ-Acc sh)
<ₛ-Acc-is-prop = all-paths-is-prop ∘ aux
  where
  aux : (sh : Shape) (ac ac' : <ₛ-Acc sh) → ac == ac'
  aux sh (acc .sh rec) (acc .sh rec') =
    ap (acc sh) (λ=₂ (λ s w → aux _ (rec s w) (rec' s w)))

<ₛ-Acc=↓ :
  ∀ {sh sh'}
  → {ac : <ₛ-Acc sh} {ac' : <ₛ-Acc sh'}
  → (p : sh == sh')
  → ac == ac' [ <ₛ-Acc ↓ p ]
<ₛ-Acc=↓ {sh} idp = prop-path (<ₛ-Acc-is-prop sh) _ _

\end{code}


Bounded shapes
--------------

"Unbundled" version.

\begin{code}

_<ₛᵇ_ : ∀ {b} → [ b ]BoundedShape → [ b ]BoundedShape → Type₀
bsh <ₛᵇ bsh' = 𝑠ℎ bsh <ₛ 𝑠ℎ bsh'

_≤ₛᵇ_ : ∀ {b} → [ b ]BoundedShape → [ b ]BoundedShape → Type₀
bsh ≤ₛᵇ bsh' = 𝑠ℎ bsh ≤ₛ 𝑠ℎ bsh'

\end{code}

"Bundled" version.

-- data _>ₛᵇ_ (bsh : BoundedShape) : BoundedShape → Type₀ where
--   on-𝑏 : ∀ {bsh'} → 𝑏 bsh > 𝑏 bsh' → bsh >ₛᵇ bsh'
--   on-𝑠ℎ : ∀ {i' h' t' s'} {u' : h' < 𝑏 bsh}
--           → let sh' = shape i' h' t' s' in
--             𝑠ℎ (𝑠ℎ𝑢 bsh) >ₛ shape i' h' t' s'
--           → bsh >ₛᵇ (𝑏 bsh ፦ sh' , u')

-- _<ₛᵇ_ : BoundedShape → BoundedShape → Type₀
-- bsh <ₛᵇ bsh' = bsh' >ₛᵇ bsh

-- <ₛᵇ-Acc = Acc BoundedShape _<ₛᵇ_

-- <ₛᵇ-is-wf-aux : ∀ b i h t s u → <ₛᵇ-Acc (b ፦ shape i h t s , u)
-- <ₛᵇ-is-wf-aux b i h t s u = acc _ (aux b i h t s u)
--   where
--   aux :
--     ∀ b i h t s u bsh'
--     → bsh' <ₛᵇ (b ፦ shape i h t s , u)
--     → <ₛᵇ-Acc bsh'
--   aux (1+ .b') i h t s u (b' ፦ shape i' h' t' s' , u') (on-𝑏 ltS) =
--     <ₛᵇ-is-wf-aux b' i' h' t' s' u'
--   aux (2+ b) i O t s u bsh' (on-𝑏 (ltSR w)) =
--     aux (1+ b) i O t s (O<S _) bsh' (on-𝑏 w)
--   aux (1+ b) i (1+ h) t s u bsh' (on-𝑏 (ltSR w)) =
--     aux b i h O (O≤ _) (<-cancel-S u) bsh' (on-𝑏 w)
--   aux b (1+ i) h t s u (b ፦ shape i h' t' s' , u') (on-𝑠ℎ (on-𝑖 ltS)) =
--     <ₛᵇ-is-wf-aux b i h' t' s' u'
--   aux b (1+ i) h t s u bsh'@(b ፦ shape _ h' _ _ , u') (on-𝑠ℎ (on-𝑖 (ltSR w))) =
--     aux b i h' O (O≤ _) u' bsh' (on-𝑠ℎ (on-𝑖 w))
--   aux b i (1+ h) t s u (b ፦ shape i h t' s' , u') (on-𝑠ℎ (on-ℎ ltS)) =
--     <ₛᵇ-is-wf-aux b i h t' s' u'
--   aux (1+ b) i (1+ h) t s u bsh' (on-𝑠ℎ (on-ℎ (ltSR w))) =
--     aux (1+ b) i h O (O≤ _) (S<-< u) bsh' (on-𝑠ℎ (on-ℎ w))
--   aux b i h (1+ t) s u (b ፦ shape i h t s' , u') (on-𝑠ℎ (on-𝑡 ltS)) =
--     <ₛᵇ-is-wf-aux b i h t s' u'
--   aux b i h (1+ t) s u bsh' (on-𝑠ℎ (on-𝑡 (ltSR w))) =
--     aux b i h t (prev-is-shape s) u bsh' (on-𝑠ℎ (on-𝑡 w))

-- <ₛᵇ-is-wf : ∀ {bsh} → <ₛᵇ-Acc bsh
-- <ₛᵇ-is-wf {b ፦ shape i h t s , u} = <ₛᵇ-is-wf-aux b i h t s u

-- open WellFoundedInduction BoundedShape _<ₛᵇ_ (λ bsh → <ₛᵇ-is-wf {bsh})
--   renaming (wf-ind to bounded-shape-ind)
--   public

-- _≤ₛᵇ_ : BoundedShape → BoundedShape → Type₀
-- bsh ≤ₛᵇ bsh' = (bsh == bsh') ⊔ (bsh <ₛᵇ bsh')
