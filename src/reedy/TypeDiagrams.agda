{-# OPTIONS --without-K #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs
open import cwfs.Contextual
open import cwfs.Pi
open import cwfs.Sigma
open import cwfs.Unit
open import cwfs.Universe

module reedy.TypeDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (ctxlstr : ContextualStructure cwfstr)
  (pistr : PiStructure cwfstr)
  (sigmastr : SigmaStructure cwfstr)
  (unitstr : UnitStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SuitableSemicategory I

open import categories.DSM (SuitableSemicategory.wildsemicatstr I)
open import reedy.LinearSieves I
open LinearSieve

open CwFStructure cwfstr
open ContextualStructure ctxlstr
open PiStructure pistr
open SigmaStructure sigmastr
open UnitStructure unitstr
open UniverseStructure univstr

SCT : ℕ → Con
A_at : (h n : ℕ) → h ≤ n → Ty (SCT n)
M[_]_at : (i : ℕ) (s : LinearSieve i) (n : ℕ) → height s ≤ n → Ty (SCT n)
M[_]-at : (i n : ℕ) → i ≤ n → Ty (SCT n)

SCT O = ◆
SCT (1+ n) = SCT n ∷ A n at n lteE

A h at .h (inl idp) = M[ h ]-at h lteE →′ U
A h at .(1+ h) (inr ltS) = A h at h lteE [ π (A h at h lteE) ]
A h at (1+ n) (inr (ltSR u)) = A h at n (inr u) [ π (A n at n lteE) ]

M[ O ]-at n _ = ⊤′
M[ 1+ i ]-at n u =
  M[ 1+ i ] linear-sieve (1+ i) i (hom-size (1+ i) i) (full-shape i)
  at n (≤-trans lteS u)

{-# TERMINATING #-}
M[ i ] s at (1+ n) (inr u) = M[ i ] s at n (<S-≤ u) [ π _ ]
M[ i ] S[ h , 1+ t ] ⦃ iS ⦄ χ χ-∋-cond at .h (inl idp) =
  Σ′ (M[ i ] linear-sieve i h t (shapeₜ↓ iS) at h lteE)
     {!!}
M[ i ] S[ 1+ h , O ] ⦃ iS ⦄ χ χ-∋-cond at .(1+ h) (inl idp) =
  M[ i ]
    S[ h , hom-size i h ] ⦃ shapeₕ↓ iS ⦄
      χ (λ f → χ-∋-cond f ∙ ! (admissible-h-iff i h f))
    at (1+ h) lteS
M[ i ] S[ O , O ] χ χ-∋-cond at .O (inl idp) = ⊤′

{- The termination pragma above is fine; we could have instead more cumbersomely used
the uncurried form:

M : (i h t : ℕ) (iS : is-shape i h t)
    (χ : DSM i)
    (χ-∋-cond :
      ∀ {m} (f : hom i m)
      → (χ ∋ f) == to-Bool (is-(i , h , t)-admissible? f))
    (n : ℕ)
    → h ≤ n
    → Ty (SCT n)
M i h t iS χ χ-∋-cond (1+ n) (inr u) =
  M i h t iS χ χ-∋-cond n (<S-≤ u) [ π _ ]
M i h (1+ t) iS χ χ-∋-cond .h (inl idp) =
  Σ′ (M[ i ] linear-sieve i h t (shapeₜ↓ iS) at h lteE)
     {!!}
M i (1+ h) O iS χ χ-∋-cond .(1+ h) (inl idp) =
  M i h (hom-size i h) (shapeₕ↓ iS)
    χ (λ f → χ-∋-cond f ∙ ! (admissible-h-iff i h f))
    (1+ h) lteS
M i O O iS χ χ-∋-cond .O (inl idp) = ⊤′
-}
