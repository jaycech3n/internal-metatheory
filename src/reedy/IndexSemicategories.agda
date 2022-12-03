{-# OPTIONS --without-K #-}

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
      → g ◦ f ≼ h ◦ f

  abstract
    endo-hom-empty : ∀ n → hom-size n n == O
    endo-hom-empty n with hom-size n n | inspect (hom-size n) n
    ... | O | _ = idp
    ... | 1+ r | have p = ⊥-rec $
      ¬< (hom-inverse n n (hom[ n , n ]# (O , transp! (O <_) p (O<S _))))

  private
    module factor-lemmas where
      abstract
        #-factors-of-≤[_]-through :
          ∀ {i h m} (t : Fin (hom-size i h)) (f : hom i m)
          → O < hom-size m h
          → ℕ -- Σ[ n ∶ ℕ ] n ≤ hom-size m h
        #-factors-of-≤[_]-through {i} {h} {m} t f u =
          #-hom[ m , h ]-from [O] st (λ α → α ◦ f ≼ [t]) (λ α → α ◦ f ≼? [t])
          -- ◂$ Σ-fmap-r λ x v → transp (λ n → n + x ≤ _) p v
          where
            [O] = hom[ m , h ]# (O , u)
            [t] = hom[ i , h ]# t

          -- p : to-ℕ (idx-of [O]) == O
          -- p = ap fst (idx-hom# (O , u))
{-
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
-}
  open factor-lemmas public
