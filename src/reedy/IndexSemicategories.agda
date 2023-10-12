{-# OPTIONS --without-K --rewriting #-}

module reedy.IndexSemicategories where

open import categories.Semicategories public
open import categories.Inverse public
open import categories.LocallyFinite public

record SuitableSemicategory ℓₘ : Type (lsuc ℓₘ) where
  field
    wildsemicatstr : WildSemicategoryStructure lzero ℓₘ ℕ
    inversestr : InverseWildSemicategoryStructure (idf ℕ) wildsemicatstr
    locfinstr : LocallyFiniteWildSemicategoryStructure wildsemicatstr

  open WildSemicategoryStructure wildsemicatstr public
  open InverseWildSemicategoryStructure inversestr public
  open LocallyFiniteWildSemicategoryStructure locfinstr public

  field
    hom-monotone :
      ∀ k m n (f : hom n m) (g h : hom m k)
      → g ≺ h
      → g ◦ f ≺ h ◦ f
