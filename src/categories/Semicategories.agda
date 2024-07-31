{-# OPTIONS --without-K --rewriting #-}

module categories.Semicategories where

open import hott.HoTT public

record WildSemicategoryStructure ℓₒ ℓₘ (Ob : Type ℓₒ) : Type (lsuc (ℓₒ ∪ ℓₘ))
  where

  infixr 80 _◦_
  field
    hom : Ob → Ob → Type ℓₘ
    _◦_ : ∀ {x y z} → hom y z → hom x y → hom x z
    ass : ∀ {x y z w} {f : hom z w} {g : hom y z} {h : hom x y}
          → (f ◦ g) ◦ h == f ◦ g ◦ h

  dom : ∀ {x y} → hom x y → Ob
  dom {x = x} _ = x

  cod : ∀ {x y} → hom x y → Ob
  cod {y = y} _ = y

  is-initial : Ob → Type (ℓₒ ∪ ℓₘ)
  is-initial x = ∀ y → is-contr (hom x y)

  is-terminal : Ob → Type (ℓₒ ∪ ℓₘ)
  is-terminal x = ∀ y → is-contr (hom y x)

  !ₜₑᵣₘ : ∀ {y} x → is-terminal x → hom y x
  !ₜₑᵣₘ x w = contr-center (w _)

  private
    module whiskering where
      _∗ₗ_ : ∀ {x y z} {f f' : hom x y} (g : hom y z) → f == f' → g ◦ f == g ◦ f'
      g ∗ₗ p = ap (g ◦_) p

      _∗ᵣ_ : ∀ {x y z} {g g' : hom y z} → g == g' → (f : hom x y) → g ◦ f == g' ◦ f
      p ∗ᵣ f = ap (_◦ f) p

      infixr 80 _∗ₗ_
      infixl 80 _∗ᵣ_

      ∗ₗ-∙ :
        ∀ {x y z} {f f' f″ : hom x y}
        → (g : hom y z) (p : f == f') (q : f' == f″)
        → g ∗ₗ (p ∙ q) == (g ∗ₗ p) ∙ (g ∗ₗ q)
      ∗ₗ-∙ g p q = ap-∙ (g ◦_) p q

      ∗ᵣ-∙ :
        ∀ {x y z} {g g' g″ : hom y z}
        → (f : hom x y) (p : g == g') (q : g' == g″)
        → (p ∙ q) ∗ᵣ f == (p ∗ᵣ f) ∙ (q ∗ᵣ f)
      ∗ᵣ-∙ f p q = ap-∙ (_◦ f) p q

      !-∗ₗ :
        ∀ {x y z} {f f' : hom x y}
        → (g : hom y z) (p : f == f')
        → ! (g ∗ₗ p) == g ∗ₗ ! p
      !-∗ₗ g p = ! $ ap-! (g ◦_) p

      !-∗ᵣ :
        ∀ {x y z} {g g' : hom y z}
        → (f : hom x y) (p : g == g')
        → ! (p ∗ᵣ f) == (! p) ∗ᵣ f
      !-∗ᵣ f p = ! $ ap-! (_◦ f) p

      ∗ₗ-∗ₗ :
        ∀ {x y z w} {f f' : hom x y}
        → (g : hom y z) (h : hom z w)
        → (p : f == f')
        → h ∗ₗ g ∗ₗ p == ! ass ∙ ((h ◦ g) ∗ₗ p) ∙ ass
      ∗ₗ-∗ₗ g h idp = ! (!-inv-l ass)

      ∗ᵣ-∗ᵣ :
        ∀ {x y z w} {h h' : hom z w}
        → (f : hom x y) (g : hom y z)
        → (p : h == h')
        → p ∗ᵣ g ∗ᵣ f == ass ∙ (p ∗ᵣ (g ◦ f)) ∙ ! ass
      ∗ᵣ-∗ᵣ f g idp = ! (!-inv-r ass)

      ∗ₗ-∗ᵣ :
        ∀ {x y z w} {g g' : hom y z}
        → (f : hom x y) (p : g == g') (h : hom z w)
        → (h ∗ₗ p) ∗ᵣ f == ass ∙ (h ∗ₗ (p ∗ᵣ f)) ∙ ! ass
      ∗ₗ-∗ᵣ f idp h = ! (!-inv-r ass)

  open whiskering public

record WildSemicategory ℓₒ ℓₘ : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  field
    Ob : Type ℓₒ
    wildsemicatstr : WildSemicategoryStructure ℓₒ ℓₘ Ob

  open WildSemicategoryStructure wildsemicatstr public
