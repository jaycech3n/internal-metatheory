{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.SimpleSemicategories

module reedy.ShapeElimination {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open SimpleSemicategory I
open import reedy.Cosieves I public

~ : ⊤
~ = unit

module _ {ℓ} (C : (i h t : ℕ) → shape i h t → Type ℓ) where
  record ShapeElimConds[i,h,t+1] {i h t} (s : shape i h (1+ t)) : Type ℓ where
    constructor •[h,h,0]_•[i,h,t]
    field
      hh0 : (t' : ℕ)
            (s' : shape h h t')
            (p : t' == O)
          → -------------------
            C h h t' s'

      iht : (s' : shape i h t)
          → ------------------
            C i h t s'

  record ShapeElimConds[i,h+1,0] {i h} (s : shape i (1+ h) O) : Type ℓ where
    constructor •[i,h,t]
    field
      iht : (t : ℕ) (s' : shape i h t)
         → --------------------------
           C i h t s'

  open ShapeElimConds[i,h,t+1]
  open ShapeElimConds[i,h+1,0]

  ShapeElimConds : (i h t : ℕ) (s : shape i h t) → Type ℓ
  ShapeElimConds i h (1+ t) s = ShapeElimConds[i,h,t+1] s → C i h (1+ t) s
  ShapeElimConds i (1+ h) O s = ShapeElimConds[i,h+1,0] s → C i (1+ h) O s
  ShapeElimConds i O O s = C i O O s

  shape-elim :
    ( ∀ (i h t : ℕ) (s : shape i h t) → ShapeElimConds i h t s)
    → (i h t : ℕ) (s : shape i h t)
    → C i h t s
  shape-elim f i h (1+ t) s =
    f i h (1+ t) s $
      •[h,h,0] (λ{ .O s' idp → shape-elim f h h O s' })
      •[i,h,t] (shape-elim f i h t)
  shape-elim f i (1+ h) O s =
    f i (1+ h) O s (•[i,h,t] (shape-elim f i h))
  shape-elim f i O O s = f i O O s
