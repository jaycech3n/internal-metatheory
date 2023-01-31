{-# OPTIONS --without-K --rewriting --experimental-lossy-unification --termination-depth=4 #-}

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.ContextDiagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves I
open SuitableSemicategory I
open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr

interleaved mutual
  SCT : ℕ → Con
  M_[_,_,_] : (n i h t : ℕ) → is-shape i h t → h < n → Con
  M⃗_[_,_,_] :
    (n i h t : ℕ) (iS : is-shape i h t) (u : h < n)
    {m : ℕ} (f : hom i m)
    {iS· : is-shape-Σ ([ i , h , t ] iS · f)}
    {u· : 2nd ([ i , h , t ] iS · f) < n}
    → let s = [ i , h , t ] iS · f in
      Sub (M n [ i , h , t ] iS u)
          (M n [ fst s , 2nd s , 3rd s ] iS· u·)
  -- Drops higher dimensional fillers
  π⋆ˢ : ∀ n h → h < n → Sub (SCT n) (SCT h)
  -- Projection from larger to smaller matching context drops components
  π⋆ᴹ_[_,_,_]→[_,_] :
    (n i h t h' t' : ℕ)
    → [ i , h' , t' ]≤ₛ[ h , t ]
    → (iS : is-shape i h t) (iS' : is-shape i h' t')
    → (u : h < n) (u' : h' < n)
    → Sub (M n [ i , h , t ] iS u) (M n [ i , h' , t' ] iS' u')
  Π′⋆_[_,_,_]→[_,_] :
    (n i h t h' t' : ℕ)
    (iS : is-shape i h t) (iS' : is-shape i h' t')
    (u : h < n) (u' : h' < n)
    → [ i , h' , t' ]≤ₛ[ h , t ]
    → Ty (M n [ i , h , t ] iS u) → Ty (M n [ i , h' , t' ] iS' u')

  SCT O = ◆

  SCT (1+ O) = ◆ ∷ U
  M 1+ O [ i , O , O ] iS u = SCT (1+ O)
  M 1+ O [ i , O , 1+ t ] iS ltS
    = M 1+ O [ i , O , t ] iS' ltS
      ∷ (var (SCT (1+ O))
          [ π⋆ᴹ 1+ O [ i , O , t ]→[ O , O ]
             (OO[≤ₛ] iS')
             iS' (empty-shape i) ltS ltS
          ]ₜ
        ◂$ coeᵀᵐ (![◦] ∙ U[])
        ◂$ el)
      where iS' = shapeₜ↓ iS
  M 1+ O [ i , 1+ h , t ] iS (ltSR ())
  π⋆ᴹ 1+ O [ i , h , t ]→[ .h , .t ] done iS iS' ltS ltS
    = id ◂$ transp-shape (λ ◻ → Sub _ (M 1+ O [ i , h , t ] ◻ ltS)) iS'
  π⋆ᴹ 1+ O [ i , .0 , .(1+ t') ]→[ .0 , t' ] (on-width ltS w) iS iS' ltS ltS
    = π _ ◂$ transp-shape (λ ◻ → Sub _ (M 1+ O [ i , O , t' ] ◻ ltS)) iS'
  π⋆ᴹ 1+ O [ i , .0 , 1+ t ]→[ .0 , t' ] (on-width (ltSR v) w) iS iS' ltS ltS
    = f
      -- ◂$ transp-shape (λ ◻ → Sub _ (M 1+ O [ i , O , t' ] ◻ ltS)) _
      where f : _
            f = {!!} ◦ˢᵘᵇ {!!}
      {-where
        iS'' : is-shape i O (1+ t')
        iS'' = shapeₜ< (<-ap-S v) iS

        f : Sub (M 1+ O [ i , O , 1+ t ] iS ltS) (M 1+ O [ i , O , {!1+ t'!} ] {!iS''!} ltS)
        f = π⋆ᴹ 1+ O [ i , O , 1+ t ]→[ O , {!1+ t'!} ] {!w!} iS {!iS''!} ltS ltS-}
  π⋆ᴹ 1+ O [ i , h , t ]→[ h' , .(hom-size i h') ] (on-height-width-max v w) iS iS' ltS ltS = {!!}
  π⋆ᴹ 1+ O [ i , h , t ]→[ h' , t' ] (on-height-width<max v v' w) iS iS' ltS ltS = {!!}
  -- transp-shape (λ ◻ → Sub _ (M 1+ O [ i , O , 1+ t ] ◻ ltS)) iS'

  SCT (2+ n) = {!!}
  M 2+ n [ i , h , t ] iS u = {!!}
  π⋆ᴹ 2+ n [ i , h , t ]→[ h' , t' ] w iS iS' u u' = {!!}
