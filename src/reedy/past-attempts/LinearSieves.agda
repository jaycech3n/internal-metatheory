{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.IndexSemicategories

module reedy.LinearSieves {ℓₘ} (I : SuitableSemicategory ℓₘ) where

open SuitableSemicategory I

record shape (i h t : ℕ) : Type₀ where
  constructor bounds
  field
    on-h : h ≤ i
    on-t : t ≤ hom-size i h
open shape public

ℕ³ = ℕ × ℕ × ℕ
Shape = Σ ℕ³ λ{ (i' , h' , t') → shape i' h' t' }
height : Shape → ℕ
height ((i , h , t) , _) = h
width : Shape → ℕ
width ((i , h , t) , _) = t

module shapes where
  empty-shape : ∀ i → shape i O O
  empty-shape i = bounds (O≤ _) (O≤ _)

  full-level : ∀ i h → h ≤ i → shape i h (hom-size i h)
  full-level i h u = bounds u lteE

  full-shape[1+_] : ∀ i → shape (1+ i) i (hom-size (1+ i) i)
  full-shape[1+ i ] = full-level (1+ i) i lteS

  top-shape : ∀ i → shape i i O
  top-shape i = bounds lteE (O≤ _)

  shapeₕ↓ : ∀ {i h} → shape i (1+ h) O → shape i h (hom-size i h)
  shapeₕ↓ (bounds on-h _) = bounds (S≤-≤ on-h) lteE

  shapeₜ↓ : ∀ {i h t} → shape i h (1+ t) → shape i h t
  shapeₜ↓ (bounds on-h on-t) = bounds on-h (S≤-≤ on-t)

open shapes public

module restriction where
  shape-∙ : (i h t : ℕ) → shape i h t
    → {j : ℕ} → h ≤ j → hom i j → ℕ × ℕ
  shape-∙ i h (1+ O) (bounds _ on-t) _ f =
    if (hom[ i , h ]# (O , S≤-< on-t) factors-through? f)
      (λ yes → h , 1)
      (λ no → h , O)
  shape-∙ i h (2+ t) sh@(bounds _ on-t) u f =
    let t' = snd (shape-∙ i h (1+ t) (shapeₜ↓ sh) u f) in
    if (hom[ i , h ]# (1+ t , S≤-< on-t) factors-through? f)
      (λ yes → h , 1+ t')
      (λ no → h , t')
  shape-∙ i (1+ h) O sh u f = shape-∙ i h (hom-size i h) (shapeₕ↓ sh) (S≤-≤ u) f
  shape-∙ i O O sh _ f = O , O

  -- Proofs that shape-∙ is again a shape
  abstract
    height-shape-∙ : (i h t : ℕ) (sh : shape i h t)
      → {j : ℕ} (u : h ≤ j) (f : hom i j)
      → fst (shape-∙ i h t sh u f) ≤ j
    height-shape-∙ i h (1+ O) (bounds _ on-t) u f
     with (hom[ i , h ]# (O , S≤-< on-t) factors-through? f)
    ... | inl yes = u
    ... | inr no = u
    height-shape-∙ i h (2+ t) (bounds _ on-t) u f
     with (hom[ i , h ]# (1+ t , S≤-< on-t) factors-through? f)
    ... | inl yes = u
    ... | inr no = u
    height-shape-∙ i (1+ h) O sh u f =
      height-shape-∙ i h (hom-size i h) (shapeₕ↓ sh) (S≤-≤ u) f
    height-shape-∙ i O O sh _ f = O≤ _

    -- By "nondegenerate" we mean a shape restriction of the form
    -- (i, h, 1+ t) ∙ f.
    height-nondeg-shape-∙ : (i h t : ℕ) (sh : shape i h (1+ t))
      → {j : ℕ} (u : h ≤ j) (f : hom i j)
      → fst (shape-∙ i h (1+ t) sh u f) == h
    height-nondeg-shape-∙ i h O (bounds _ on-t) u f
     with (hom[ i , h ]# (O , S≤-< on-t) factors-through? f)
    ... | inl yes = idp
    ... | inr no = idp
    height-nondeg-shape-∙ i h (1+ t) (bounds _ on-t) u f
     with (hom[ i , h ]# (1+ t , S≤-< on-t) factors-through? f)
    ... | inl yes = idp
    ... | inr no = idp

    postulate
      width-shape-∙ : (i h t : ℕ) (sh : shape i h t)
        → {j : ℕ} (u : h ≤ j) (f : hom i j)
        → let h' , t' = shape-∙ i h t sh u f in t' ≤ hom-size j h'
    -- width-shape-∙ i h (1+ O) (bounds _ on-t) u f
    --  with (hom[ i , h ]# (O , S≤-< on-t) factors-through? f)
    -- ... | inl yes = {!!}
    -- ... | inr no = O≤ _
    -- width-shape-∙ i h (2+ t) sh@(bounds _ on-t) {j} u f
    --  with (hom[ i , h ]# (1+ t , S≤-< on-t) factors-through? f)
    -- ... | inl yes = {!!}
    -- ... | inr no =
    --         width-shape-∙ i h (1+ t) (shapeₜ↓ sh) u f
    --         ◂$ transp (λ ◻ → snd (shape-∙ i h (1+ t) _ u f) ≤ hom-size j ◻) p
    --         where
    --         p : fst (shape-∙ i h (1+ t) (shapeₜ↓ sh) u f) == h
    --         p = height-nondeg-shape-∙ i h t (shapeₜ↓ sh) u f
    -- width-shape-∙ i (1+ h) O sh u f =
    --   width-shape-∙ i h (hom-size i h) (shapeₕ↓ sh) (S≤-≤ u) f
    -- width-shape-∙ i O O sh _ f = O≤ _

    ∙-shape : (i h t : ℕ) (sh : shape i h t)
      → {j : ℕ} (u : h ≤ j) (f : hom i j)
      → let h' , t' = shape-∙ i h t sh u f in shape j h' t'
    ∙-shape i h t sh u f =
      bounds (height-shape-∙ i h t sh u f) (width-shape-∙ i h t sh u f)

  [_,_,_]_∙ : (i h t : ℕ) (sh : shape i h t)
    → {j : ℕ} (u : h ≤ j) (f : hom i j)
    → Shape
  [ i , h , t ] sh ∙ {j} u f = (j , shape-∙ i h t sh u f) , ∙-shape i h t sh u f

open restriction public
