{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories

module categories.CommutingShapes {ℓₒ ℓₘ} (𝒞 : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory 𝒞

record CSh : Type (ℓₒ ∪ ℓₘ) where
  constructor commshape
  field
    src tgt : Ob
    fst snd : hom src tgt
    comm : fst == snd

record CSq : Type (ℓₒ ∪ ℓₘ) where
  constructor square
  field
    tl tr bl br : Ob
    t : hom tl tr
    b : hom bl br
    l : hom tl bl
    r : hom tr br
    comm : r ◦ t == b ◦ l

CSq-CSh : CSq → CSh
CSq-CSh (square tl tr bl br t b l r comm) =
  commshape tl br (r ◦ t) (b ◦ l) comm

-- Everything from here is what we want to define pullbacks. Do we need
-- everything above?

record CSq-on (tl tr bl br : Ob) (r : hom tr br) (b : hom bl br)
  : Type (ℓₒ ∪ ℓₘ)
  where
  constructor square
  field
    t : hom tl tr
    l : hom tl bl
    comm : r ◦ t == b ◦ l

CSq-precomp :
  ∀ {A' A B C D : Ob} {g : hom B D} {k : hom C D}
  → hom A' A
  → CSq-on A B C D g k
  → CSq-on A' B C D g k
CSq-precomp {g = g} {k} m (square f h comm) =
  square (f ◦ m) (h ◦ m) p
  where
  p : g ◦ f ◦ m == k ◦ h ◦ m
  p = ! ass ∙ ap (_◦ m) comm ∙ ass
