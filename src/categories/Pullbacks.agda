{-# OPTIONS --without-K --rewriting #-}

open import categories.Semicategories

module categories.Pullbacks {ℓₒ ℓₘ} (C : WildSemicategory ℓₒ ℓₘ) where

open WildSemicategory C

is-comm-sq : ∀ {w x y z}
  → hom w x → hom x z → hom w y → hom y z
  → Type ℓₘ
is-comm-sq u f v g = f ◦ u == g ◦ v

pullback-up : ∀ {w x y z}
  → hom w x → hom x z → hom w y → hom y z
  → Type (ℓₒ ∪ ℓₘ)
pullback-up {w} {x} {y} u f v g =
  (w' : Ob) (u' : hom w' x) (v' : hom w' y)
  → is-comm-sq u' f v' g
  → is-contr (Σ[ h ː hom w' w ] (u' == u ◦ h) × (v' == v ◦ h))

is-pullback : ∀ {w x y z}
  → (u : hom w x) (f : hom x z) (v : hom w y) (g : hom y z)
  → Type (ℓₒ ∪ ℓₘ)
is-pullback u f v g = is-comm-sq u f v g × pullback-up u f v g

pullback-pasting-2 :
  ∀ {x y z x' y' z'}
  → (f : hom x y) (g : hom y z) (f' : hom x' y') (g' : hom y' z')
  → (hx : hom x' x) (hy : hom y' y) (hz : hom z' z)
  → is-pullback g' hz hy g
  → is-pullback (g' ◦ f') hz hx (g ◦ f)
  → is-comm-sq f' hy hx f
  → pullback-up f' hy hx f
pullback-pasting-2
  f g f' g'
  hx hy hz
  (commr , pbr)
  (commo , pbo)
  comml
  w' u' v' comm = {!!}
  where

