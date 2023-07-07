{-# OPTIONS --without-K --rewriting #-}

module reedy.IndexSemicategories where

open import categories.Semicategories public
open import categories.LocallyFinite public
open import categories.Inverse public

record SuitableSemicategory ℓₘ : Type (lsuc ℓₘ) where
  field
    wildsemicatstr : WildSemicategoryStructure lzero ℓₘ ℕ
    locfinstr : LocallyFinitelyIndexedWildSemicategoryStructure wildsemicatstr
    inversestr : InverseWildSemicategoryStructure (idf ℕ) wildsemicatstr

  open WildSemicategoryStructure wildsemicatstr public
  open InverseWildSemicategoryStructure inversestr public
  open LocallyFinitelyIndexedWildSemicategoryStructure locfinstr public

  field
    hom-monotone :
      ∀ k m n (f : hom n m) (g h : hom m k)
      → g ≺ h
      → g ◦ f ≺ h ◦ f
      -- → g ◦ f ≼ h ◦ f -- could in principle generalize to weakly monotone

  abstract
    endo-hom-empty : ∀ n → hom-size n n == O
    endo-hom-empty n with hom-size n n | inspect (hom-size n) n
    ... | O | _ = idp
    ... | 1+ r | have p = ⊥-rec $
      ¬< (hom-inverse n n (hom[ n , n ]# (O , transp! (O <_) p (O<S _))))

  {-
  private
    module factor-lemmas where
      #-factors-monotone :
        ∀ {i h m} (f : hom i m) (u : O < hom-size m h)
          (s t : Fin (hom-size i h))
        → s ≤-Fin t
        → #-factors-of-≤[ s ]-through f u ≤ #-factors-of-≤[ t ]-through f u
      #-factors-monotone f u s t (inl idp) =
        transp (λ ◻ → #-factors-of-≤[ ◻ ]-through f u ≤ #-factors-of-≤[ t ]-through f u)
          (Fin= idp) lteE
      #-factors-monotone f u s (.(1+ (fst s)) , v) (inr ltS) = {!!}
      #-factors-monotone f u s (1+ t , v) (inr (ltSR w)) =
        ≤-trans
          (#-factors-monotone f u s (t , <-trans ltS v) (inr w))
          (#-factors-monotone f u (t , <-trans ltS v) (1+ t , v) (inr ltS))

  open factor-lemmas public
  -}
