{-# OPTIONS --without-K --rewriting #-}

open import categories.Categories

module categories.Equivalence {ℓₒ ℓₘ} {Ob : Type ℓₒ}
  (wildcatstr : WildCategoryStructure ℓₒ ℓₘ Ob)
  where

open WildCategoryStructure wildcatstr

module _ {x} {y} (f : hom x y) where
  is-wild-iso : Type ℓₘ
  is-wild-iso = Σ[ g ﹕ hom y x ] (g ◦ f == id) × (f ◦ g == id)

  is-wild-eqv : Type ℓₘ
  is-wild-eqv = (Σ[ r ﹕ hom y x ] r ◦ f == id) × (Σ[ s ﹕ hom y x ] f ◦ s == id)
  -- Σ (hom y x) λ s → Σ (hom y x) λ r → (r ◦ f == id) × (f ◦ s == id)

  is-wild-iso-is-wild-eqv : is-wild-iso → is-wild-eqv
  is-wild-iso-is-wild-eqv (g , p , q) = (g , p) , g , q

  module _ {s r : hom y x} (p : r ◦ f == id) (q : f ◦ s == id) where
    sec-ret-zigzag-ret : r ◦ f ◦ s == r
    sec-ret-zigzag-ret = (r ∗ₗ q) ∙ idr _

    sec-ret-zigzag-sec : r ◦ f ◦ s == s
    sec-ret-zigzag-sec = ! ass ∙ (p ∗ᵣ s) ∙ idl _

  is-wild-eqv-is-wild-iso : is-wild-eqv → is-wild-iso
  is-wild-eqv-is-wild-iso ((r , p) , s , q) = r ◦ f ◦ s , p' , q'
    where
    p' : (r ◦ f ◦ s) ◦ f == id
    p' = (sec-ret-zigzag-ret p q ∗ᵣ f) ∙ p

    q' : f ◦ (r ◦ f ◦ s) == id
    q' = (f ∗ₗ sec-ret-zigzag-sec p q) ∙ q

-- In precategories,
module _ (h : ∀ x y → is-set (hom x y)) where
  is-wild-iso≃is-wild-eqv-precat :
    ∀ {x} {y} (f : hom x y)
    → is-wild-iso f ≃ is-wild-eqv f
  is-wild-iso≃is-wild-eqv-precat {x} {y} f =
    equiv (is-wild-iso-is-wild-eqv f) (is-wild-eqv-is-wild-iso f)
    (λ{((r , p) , s , q) → ×ΣΣ=
        (sec-ret-zigzag-ret f p q)
        (prop-has-all-paths-↓ ⦃ set-equality-is-prop ⦃ h x x ⦄ ⦄)
        (sec-ret-zigzag-sec f p q)
        (prop-has-all-paths-↓ ⦃ set-equality-is-prop ⦃ h y y ⦄ ⦄) })
    (λ{(g , p , q) → Σ×=
      ((g ∗ₗ q) ∙ idr _)
      (prop-has-all-paths-↓ ⦃ set-equality-is-prop ⦃ h x x ⦄ ⦄)
      (prop-has-all-paths-↓ ⦃ set-equality-is-prop ⦃ h y y ⦄ ⦄) })

_wild≃_ : Ob → Ob → Type _
x wild≃ y = Σ (hom x y) is-wild-eqv

_wild≅_ : Ob → Ob → Type _
x wild≅ y = Σ (hom x y) is-wild-iso

wild≅-to-wild∼≃ : ∀ {x y} → x wild≅ y → x wild≃ y
wild≅-to-wild∼≃ (f , g , gret , gsec) = f , (g , gret) , (g , gsec)

id-to-wild≅ : ∀ {x y} → x == y → x wild≅ y
id-to-wild≅ p = idd p , idd (! p) , idd-sec p , idd-ret p

id-to-wild≃ : ∀ {x y} → x == y → x wild≃ y
id-to-wild≃ = wild≅-to-wild∼≃ ∘ id-to-wild≅

private
  tmp : ∀ {x y} (p : x == y) → id-to-wild≃ p == (idd p , _)
  tmp p = idp


{- Univalence -}

Wild-Univalence : Type _
Wild-Univalence = ∀ {x y} → is-equiv (id-to-wild≃ {x = x} {y})

module univalence (uni : Wild-Univalence) where
  wild-ua : ∀ {x y} → x wild≃ y → x == y
  wild-ua = is-equiv.g uni

  wild-ua-sec : ∀ {x y} → id-to-wild≃ ∘ wild-ua ∼ idf (x wild≃ y)
  wild-ua-sec = is-equiv.f-g uni

  idd-ua :
    ∀ {x y} (f : hom x y) (e : is-wild-eqv f)
    → idd (wild-ua (f , e)) == f
  idd-ua f e = ap fst (wild-ua-sec (f , e))
