{-# OPTIONS --without-K #-}

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Sigma
open import cwfs.Unit
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.TypeDiagrams {ℓₘᴵ ℓₒ ℓₘ ℓᵀʸ ℓᵀᵐ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure ℓᵀʸ ℓᵀᵐ C)
  (pistr : PiStructure cwfstr)
  (sigmastr : SigmaStructure cwfstr)
  (unitstr : UnitStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves I
open SuitableSemicategory I
open CwFStructure cwfstr
open PiStructure pistr
open SigmaStructure sigmastr
open UnitStructure unitstr
open UniverseStructure univstr

SCT : ℕ → Con
M_at : (n n⁺ : ℕ) → n ≤ n⁺ → Ty (SCT n⁺)

[_]-fillers-at : (n n⁺ : ℕ) → n ≤ n⁺ → Ty (SCT n⁺)
[ n ]-fillers-at n⁺ u = M n at n⁺ u →′ U

SCT O = ◆
SCT (1+ n) = SCT n ∷ [ n ]-fillers-at n lteE

M[_,_,_]_at : (i h t : ℕ) → is-shape i h t → (n : ℕ) → h ≤ n → Ty (SCT n)
M[ i , h , 1+ t ] iS at n u =
  Σ′(M[ i , h , t ] shape-from-next-t iS at n u)
    {!!}
M[ i , 1+ h , O ] iS at n u =
  M[ i , h , hom-size i h ]
    shape-from-next-h iS
    at n (≤-trans lteS u)
M[ i , O , O ] iS at n u = ⊤′

M O at n⁺ u = ⊤′
M 1+ n at n⁺ u =
  M[ 1+ n , n , hom-size (1+ n) n ]
    full-shape (1+ n) n ltS
    at n⁺ (≤-trans lteS u)
