{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.IndexSemicategories

module reedy.LinearSievesDev {ℓₘ} (I : SuitableSemicategory ℓₘ) where

open SuitableSemicategory I

width-of-[_,_,_]∙ : ∀ i h t {j} → hom i j → t ≤ hom-size i h → ℕ
width-of-[ i , h , 0 ]∙ f b = 0
width-of-[ i , h , 1+ t ]∙ f b =
  if f ∣ hom[ i , h ]# (t , S≤-< b)
  then (λ _ → 1+ rec)
  else λ _ → rec
  where
  rec = width-of-[ i , h , t ]∙ f (S≤-≤ b)

abstract
  width-[_,_,_]∙_-top :
    ∀ i h t (f : hom i h) (b : t ≤ hom-size i h)
    → width-of-[ i , h , t ]∙ f b == 0
  width-[ i , h , O ]∙ f -top b = idp
  width-[ i , h , 1+ t ]∙ f -top b with f ∣ hom[ i , h ]# (t , S≤-< b)
  ... | inl (g , _) = ⊥-rec (endo-hom-empty g)
  ... | inr x = width-[ i , h , t ]∙ f -top (S≤-≤ b)

module _ {i j h : ℕ} {u : O < hom-size j h} where
  [_,_]/_ : (t : ℕ) → t < hom-size i h → hom i j → hom j h
  [ O , v ]/ f =
    if f ∣ hom[ i , h ]# (0 , v)
    then (λ{ (g , _) → g })
    else λ _ → hom[ j , h ]# (0 , u)
  [ 1+ t , v ]/ f = {!!}
