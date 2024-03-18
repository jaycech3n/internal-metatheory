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
