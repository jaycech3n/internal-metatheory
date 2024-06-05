Well founded orders on shapes
=============================

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

open import reedy.SimpleSemicategories

module reedy.ShapeOrder {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open import hott.WellFounded
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

≤ₛ-<ₛ-≤ₛ :  ∀ {sh sh' sh''} → sh ≤ₛ sh' → sh' <ₛ sh'' → sh ≤ₛ sh''
≤ₛ-<ₛ-≤ₛ u v = ≤ₛ-trans u (inr v)

𝑖-≤ₛ : ∀ {sh sh'} → sh ≤ₛ sh' → 𝑖 sh ≤ 𝑖 sh'
𝑖-≤ₛ (inl idp) = lteE
𝑖-≤ₛ (inr (on-𝑖 w)) = inr w
𝑖-≤ₛ (inr (on-ℎ _)) = lteE
𝑖-≤ₛ (inr (on-𝑡 _)) = lteE

\end{code}

Equivalent form of _<ₛ_.

\begin{code}

_<ₛ'_ : Shape → Shape → Type₀
sh <ₛ' sh' = (𝑖 sh < 𝑖 sh')
             ⊔ ((𝑖 sh == 𝑖 sh') × (ℎ sh < ℎ sh'))
             ⊔ ((𝑖 sh == 𝑖 sh') × (ℎ sh == ℎ sh') × (𝑡 sh < 𝑡 sh'))

<ₛ'≃<ₛ : ∀ sh sh' → (sh <ₛ' sh') ≃ (sh <ₛ sh')
<ₛ'≃<ₛ sh sh' = equiv f g
  (λ{ (on-𝑖 x) → idp ; (on-ℎ x) → idp ; (on-𝑡 x) → idp })
  (λ{ (inl x) → idp
    ; (inr (inl (idp , u))) → idp
    ; (inr (inr (idp , idp , u))) → idp })
  where
  f : sh <ₛ' sh' → sh <ₛ sh'
  f (inl u) = on-𝑖 u
  f (inr (inl (idp , u))) = on-ℎ u
  f (inr (inr (idp , idp , u))) = on-𝑡 u

  g : sh <ₛ sh' → sh <ₛ' sh'
  g (on-𝑖 u) = inl u
  g (on-ℎ u) = inr (inl (idp , u))
  g (on-𝑡 u) = inr (inr (idp , idp , u))

\end{code}

<ₛ and ≤ₛ are propositions.

\begin{code}

abstract
  <ₛ'-has-all-paths : (sh sh' : Shape) → has-all-paths (sh <ₛ' sh')
  <ₛ'-has-all-paths _ _ (inl u) (inl v) = ap inl (<-has-all-paths u v)
  <ₛ'-has-all-paths _ _ (inl u) (inr (inl (idp , _))) = ⊥-rec $ ¬<-self u
  <ₛ'-has-all-paths _ _ (inl u) (inr (inr (idp , _))) = ⊥-rec $ ¬<-self u
  <ₛ'-has-all-paths _ _ (inr (inl (idp , _))) (inl v) = ⊥-rec $ ¬<-self v
  <ₛ'-has-all-paths _ _ (inr (inr (idp , _))) (inl v) = ⊥-rec $ ¬<-self v
  <ₛ'-has-all-paths _ _ (inr (inl u)) (inr (inl v)) =
    ap (inr ∘ inl) $ prop-path (×-level ℕ-id-is-prop <-is-prop) u v
  <ₛ'-has-all-paths _ _ (inr (inl (idp , u))) (inr (inr (_ , idp , _))) =
    ⊥-rec $ ¬<-self u
  <ₛ'-has-all-paths _ _ (inr (inr (idp , idp , _))) (inr (inl (_ , v))) =
    ⊥-rec $ ¬<-self v
  <ₛ'-has-all-paths _ _ (inr (inr u)) (inr (inr v)) =
    ap (inr ∘ inr) $
      prop-path (×-level ℕ-id-is-prop (×-level ℕ-id-is-prop <-is-prop)) u v
    -- Should probably fix the instance search for hlevel witnesses...

-- Use univalence here, but not necessary.
<ₛ-has-all-paths : (sh sh' : Shape) → has-all-paths (sh <ₛ sh')
<ₛ-has-all-paths sh sh' =
  transp has-all-paths (ua (<ₛ'≃<ₛ sh sh')) (<ₛ'-has-all-paths sh sh')

\end{code}

Inequalities.

Need all the following for the recursion in the diagram construction.

\begin{code}

≤ₛ𝑡 : ∀ {i h t t' s s'} → t' ≤ t → shape i h t' s' ≤ₛ shape i h t s
≤ₛ𝑡 (inl idp) = inl (Shape= _ _ _)
≤ₛ𝑡 (inr u) = inr (on-𝑡 u)

<ₛS𝑡-≤ₛ𝑡 :
  ∀ {i h t s s'} sh
  → sh <ₛ shape i h (1+ t) s
  → sh ≤ₛ shape i h t s'
<ₛS𝑡-≤ₛ𝑡 _ (on-𝑖 u) = inr (on-𝑖 u)
<ₛS𝑡-≤ₛ𝑡 _ (on-ℎ u) = inr (on-ℎ u)
<ₛS𝑡-≤ₛ𝑡 _ (on-𝑡 u) = ≤ₛ𝑡 (<S-≤ u)

<ₛSℎ0-≤ₛℎfull :
  ∀ {i h s s'} sh
  → sh <ₛ shape i (1+ h) O s
  → sh ≤ₛ shape i h (hom-size i h) s'
<ₛSℎ0-≤ₛℎfull _ (on-𝑖 u) = inr (on-𝑖 u)
<ₛSℎ0-≤ₛℎfull (shape _ _ _ s) (on-ℎ ltS) = ≤ₛ𝑡 s
<ₛSℎ0-≤ₛℎfull _ (on-ℎ (ltSR u)) = inr (on-ℎ u)

bdd-<ₛS𝑖00-≤ₛ𝑖bfull :
  ∀ {b i s s'} (sh : Shape) (u : ℎ sh < 1+ b)
  → sh <ₛ shape (1+ i) O O s
  → sh ≤ₛ shape i b (hom-size i b) s'
bdd-<ₛS𝑖00-≤ₛ𝑖bfull _ _ (on-𝑖 (ltSR v)) = inr (on-𝑖 v)
bdd-<ₛS𝑖00-≤ₛ𝑖bfull (shape _ _ _ s) ltS (on-𝑖 ltS) = ≤ₛ𝑡 s
bdd-<ₛS𝑖00-≤ₛ𝑖bfull _ (ltSR u) (on-𝑖 ltS) = inr (on-ℎ u)

\end{code}

Well foundedness of <ₛ.

\begin{code}

<ₛ-Acc = Acc Shape _<ₛ_

rec-of : ∀ {sh} → <ₛ-Acc sh → _
rec-of (acc _ rec) = rec

<ₛ-Accc : ∀ i h t s → Type₀
<ₛ-Accc i h t s = <ₛ-Acc (shape i h t s)

<ₛ-wf-aux : ∀ i h t s → <ₛ-Acc (shape i h t s)
<ₛ-wf-aux i h t s = acc _ (aux i h t s)
  where
  -- By case distinction on the proof of <ₛ
  aux : ∀ i h t s → ∀ sh' → sh' <ₛ shape i h t s → <ₛ-Acc sh'
  aux .(1+ i') h t s (shape i' h' t' s') (on-𝑖 ltS) = <ₛ-wf-aux i' h' t' s'
  aux (1+ i) h t s sh' (on-𝑖 (ltSR w)) = aux i O O (O≤ _) sh' (on-𝑖 w)
  aux i h t s (shape .i h' t' s') (on-ℎ ltS) = <ₛ-wf-aux i h' t' s'
  aux i (1+ h) t s sh' (on-ℎ (ltSR w)) = aux i h O (O≤ _) sh' (on-ℎ w)
                                         -- could also use (i, h, full)
  aux i h .(1+ _) s (shape i h t' s') (on-𝑡 ltS) = <ₛ-wf-aux i h t' s'
  aux i h (1+ t) s sh' (on-𝑡 (ltSR w)) = aux i h t (prev-is-shape s) sh' (on-𝑡 w)

<ₛ-wf : ∀ {sh} → <ₛ-Acc sh
<ₛ-wf {shape i h t s} = <ₛ-wf-aux i h t s

open WellFoundedInduction Shape _<ₛ_ (λ sh → <ₛ-wf {sh})
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

Parametrized over a bound b on the shape height.

\begin{code}

_<ₛᵇ_ : ∀ {b} → [ b ]BoundedShape → [ b ]BoundedShape → Type₀
(sh , _) <ₛᵇ (sh' , _) = sh <ₛ sh'

_≤ₛᵇ_ : ∀ {b} → [ b ]BoundedShape → [ b ]BoundedShape → Type₀
(sh , _) ≤ₛᵇ (sh' , _) = sh ≤ₛ sh'

<ₛᵇ-Acc : ∀ {b} → [ b ]BoundedShape → Type₀
<ₛᵇ-Acc {b} = Acc [ b ]BoundedShape (_<ₛᵇ_ {b})

<ₛᵇ-wf : ∀ {b} {bsh : [ b ]BoundedShape} → <ₛᵇ-Acc bsh
<ₛᵇ-wf {b} {bsh} =
  <Σ-preserves-all-acc (λ sh → ℎ sh < b) _<ₛ_ (λ sh → <ₛ-wf {sh}) bsh

\end{code}


Bundled version; not used.

--```
data _>ₛᵇ_ (bsh : BoundedShape) : BoundedShape → Type₀ where
  on-𝑏 : ∀ {bsh'} → 𝑏 bsh > 𝑏 bsh' → bsh >ₛᵇ bsh'
  on-𝑠ℎ : ∀ {i' h' t' s'} {u' : h' < 𝑏 bsh}
          → let sh' = shape i' h' t' s' in
            𝑠ℎ (𝑠ℎ𝑢 bsh) >ₛ shape i' h' t' s'
          → bsh >ₛᵇ (𝑏 bsh ፦ sh' , u')

_<ₛᵇ_ : BoundedShape → BoundedShape → Type₀
bsh <ₛᵇ bsh' = bsh' >ₛᵇ bsh

<ₛᵇ-Acc = Acc BoundedShape _<ₛᵇ_

<ₛᵇ-wf-aux : ∀ b i h t s u → <ₛᵇ-Acc (b ፦ shape i h t s , u)
<ₛᵇ-wf-aux b i h t s u = acc _ (aux b i h t s u)
  where
  aux :
    ∀ b i h t s u bsh'
    → bsh' <ₛᵇ (b ፦ shape i h t s , u)
    → <ₛᵇ-Acc bsh'
  aux (1+ .b') i h t s u (b' ፦ shape i' h' t' s' , u') (on-𝑏 ltS) =
    <ₛᵇ-wf-aux b' i' h' t' s' u'
  aux (2+ b) i O t s u bsh' (on-𝑏 (ltSR w)) =
    aux (1+ b) i O t s (O<S _) bsh' (on-𝑏 w)
  aux (1+ b) i (1+ h) t s u bsh' (on-𝑏 (ltSR w)) =
    aux b i h O (O≤ _) (<-cancel-S u) bsh' (on-𝑏 w)
  aux b (1+ i) h t s u (b ፦ shape i h' t' s' , u') (on-𝑠ℎ (on-𝑖 ltS)) =
    <ₛᵇ-wf-aux b i h' t' s' u'
  aux b (1+ i) h t s u bsh'@(b ፦ shape _ h' _ _ , u') (on-𝑠ℎ (on-𝑖 (ltSR w))) =
    aux b i h' O (O≤ _) u' bsh' (on-𝑠ℎ (on-𝑖 w))
  aux b i (1+ h) t s u (b ፦ shape i h t' s' , u') (on-𝑠ℎ (on-ℎ ltS)) =
    <ₛᵇ-wf-aux b i h t' s' u'
  aux (1+ b) i (1+ h) t s u bsh' (on-𝑠ℎ (on-ℎ (ltSR w))) =
    aux (1+ b) i h O (O≤ _) (S<-< u) bsh' (on-𝑠ℎ (on-ℎ w))
  aux b i h (1+ t) s u (b ፦ shape i h t s' , u') (on-𝑠ℎ (on-𝑡 ltS)) =
    <ₛᵇ-wf-aux b i h t s' u'
  aux b i h (1+ t) s u bsh' (on-𝑠ℎ (on-𝑡 (ltSR w))) =
    aux b i h t (prev-is-shape s) u bsh' (on-𝑠ℎ (on-𝑡 w))

<ₛᵇ-wf : ∀ {bsh} → <ₛᵇ-Acc bsh
<ₛᵇ-wf {b ፦ shape i h t s , u} = <ₛᵇ-wf-aux b i h t s u

open WellFoundedInduction BoundedShape _<ₛᵇ_ (λ bsh → <ₛᵇ-wf {bsh})
  renaming (wf-ind to bounded-shape-ind)
  public

_≤ₛᵇ_ : BoundedShape → BoundedShape → Type₀
bsh ≤ₛᵇ bsh' = (bsh == bsh') ⊔ (bsh <ₛᵇ bsh')
--```
