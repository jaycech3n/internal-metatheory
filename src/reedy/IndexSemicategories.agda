{-# OPTIONS --without-K #-}

module reedy.IndexSemicategories where

open import categories.Semicategories public
open import categories.LocallyFinite public
open import categories.Inverse public

record SuitableSemicategory ℓₘ : Type (lsuc ℓₘ) where
  field
    C : WildSemicategoryStructure lzero ℓₘ ℕ
    C-loc-fin : LocallyFiniteOrderedWildSemicategoryStructure C
    C-inverse : InverseWildSemicategoryStructure C

  open WildSemicategoryStructure C public
  open InverseWildSemicategoryStructure C-inverse public
  open LocallyFiniteOrderedWildSemicategoryStructure C-loc-fin public

  field
    hom-monotone :
      ∀ k m n (f : hom n m) (g h : hom m k)
      → g ≺ h
      → g ◦ f ≼ h ◦ f

  abstract
    endo-hom-empty : ∀ n → hom-size n n == O
    endo-hom-empty n with hom-size n n | inspect (hom-size n) n
    ... | O | _ = idp
    ... | 1+ r | have p =
      ¬< (hom-inverse n n (hom[ n , n ]# (O , transp! (O <_) p (O<S _))))
        ◅ ⊥-rec
