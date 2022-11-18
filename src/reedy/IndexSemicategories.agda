{-# OPTIONS --without-K #-}

module reedy.IndexSemicategories where

open import categories.Semicategories public
open import categories.LocallyFinite public
open import categories.Inverse public

record SuitableSemicategory ℓₘ : Type (lsuc ℓₘ) where
  field
    wildsemicatstr : WildSemicategoryStructure lzero ℓₘ ℕ
    locfinstr : LocallyFinitelyIndexedWildSemicategoryStructure wildsemicatstr
    inversestr : InverseWildSemicategoryStructure wildsemicatstr

  open WildSemicategoryStructure wildsemicatstr public
  open InverseWildSemicategoryStructure inversestr public
  open LocallyFinitelyIndexedWildSemicategoryStructure locfinstr public

  field
    hom-monotone :
      ∀ k m n (f : hom n m) (g h : hom m k)
      → g ≺ h
      → g ◦ f ≼ h ◦ f

  abstract
    endo-hom-empty : ∀ n → hom-size n n == O
    endo-hom-empty n with hom-size n n | inspect (hom-size n) n
    ... | O | _ = idp
    ... | 1+ r | have p = ⊥-rec $
      ¬< (hom-inverse n n (hom[ n , n ]# (O , transp! (O <_) p (O<S _))))
