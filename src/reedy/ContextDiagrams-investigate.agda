{-# OPTIONS --without-K --rewriting --experimental-lossy-unification -vterm:50 -vterm.found.call:20 #-}

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.ContextDiagrams-investigate {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves-investigate I
open SuitableSemicategory I
open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr

interleaved mutual
  SCT : ℕ → Con
  M_[_,_,_] : (n i h t : ℕ) → h < n → Con
  -- Projection from larger to smaller matching context drops components
  π⋆_[_,_,_]→[_,_] :
    (n i h t h' t' : ℕ)
    → (h' , t') ≤ₛ+ (h , t)
    → (u : h < n) (u' : h' < n)
    → Sub (M n [ i , h , t ] u) (M n [ i , h' , t' ] u')

  -- n = 0
  SCT O = ◆

  -- n = 1
  SCT (1+ O) = ◆ ∷ U

  M 1+ O [ i , O , O ] ltS = SCT (1+ O)
  M 1+ O [ i , O , 1+ t ] ltS
    = M 1+ O [ i , O , t ] ltS
      ∷ (var (SCT (1+ O))
          [ π⋆ 1+ O [ i , O , t ]→[ O , O ]
            {!≤ₛ-≤ₛ+ (O , O) (O , t) (inr (idp , O≤ t))!}
            ltS ltS
          ]ₜ
        ◂$ coeᵀᵐ (![◦] ∙ U[])
        ◂$ el)

  π⋆ 1+ O [ i , h , t ]→[ .h , .t ] done ltS ltS = id
  π⋆ 1+ O [ i , h , t ]→[ h' , t' ] (on-height ()) ltS ltS
  π⋆ 1+ O [ i , O , t ]→[ .O , t' ] (on-width w) ltS ltS
    = π _ ◦ˢᵘᵇ π⋆ 1+ O [ i , O , t ]→[ O , 1+ t' ] w ltS ltS

  -- n > 1
  SCT (2+ n) = {!!}
  M 2+ n [ i , h , t ] u = {!!}
  π⋆ 2+ n [ i , h , t ]→[ h' , t' ] w u u' = {!!}
