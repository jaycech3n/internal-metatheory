{-# OPTIONS --without-K --rewriting #-}

module reedy.SimpleSemicategories where

open import categories.Semicategories public
open import categories.Inverse public
open import categories.LocallyFinite public

record SimpleSemicategory ℓₘ : Type (lsuc ℓₘ) where
  field
    wildsemicatstr : WildSemicategoryStructure lzero ℓₘ ℕ
    inversestr : InverseWildSemicategoryStructure (idf ℕ) wildsemicatstr
    locfinstr : LocallyFiniteWildSemicategoryStructure wildsemicatstr

  open WildSemicategoryStructure wildsemicatstr public
  open InverseWildSemicategoryStructure inversestr public
  open LocallyFiniteWildSemicategoryStructure locfinstr public

  private
    module definitions where
      monotone-precomp : ∀ {i j} (f : hom i j) → Type ℓₘ
      monotone-precomp {j = j} f =
        ∀ {k} (g h : hom j k)
        → g ≺ h
        → g ◦ f ≺ h ◦ f

  open definitions public

  private
    module lemmas where
      ¬divides-same-target :
        ∀ i j t (u : t < hom-size i j) (f : hom i j)
        → ¬ (f divides #[ t ] i j u)
      ¬divides-same-target i j t u f (g , _) = endo-hom-empty g

  open lemmas public

module IsStrictlyOriented {ℓₘ}
  (C : SimpleSemicategory ℓₘ)
  (precomp-monotone : ∀ {m n} (f : SimpleSemicategory.hom C m n)
    → SimpleSemicategory.monotone-precomp C f)
  where
  open SimpleSemicategory C

  abstract
    hom-is-epi : ∀ {l m n} (f : hom l m) (g h : hom m n)
      → g ◦ f == h ◦ f
      → g == h
    hom-is-epi f g h p = ⊔-rec
      (idf _)
      (λ{ (inl u) → ⊥-rec $
            ¬≺-self _ (transp (_≺ h ◦ f) p (precomp-monotone f g h u))
        ; (inr u) → ⊥-rec $
            ¬≺-self _ (transp (h ◦ f ≺_) p (precomp-monotone f h g u)) })
      $ ≺-trichotomy g h

    ≺-cancel-r : ∀ {l m n} (f : hom l m) (g h : hom m n)
      → g ◦ f ≺ h ◦ f
      → g ≺ h
    ≺-cancel-r f g h u with ≺-trichotomy g h
    ... | inl idp = ⊥-rec (¬≺-self _ u)
    ... | inr (inl v) = v
    ... | inr (inr v) = ⊥-rec $ ¬≺-self _ $ <-trans (precomp-monotone f h g v) u

    ≼-cancel-r : ∀ {l m n} (f : hom l m) (g h : hom m n)
      → g ◦ f ≼ h ◦ f
      → g ≼ h
    ≼-cancel-r f g h (inl p) = =-≼ (hom-is-epi _ _ _ (hom= p))
    ≼-cancel-r f g h (inr u) = inr (≺-cancel-r _ _ _ u)
