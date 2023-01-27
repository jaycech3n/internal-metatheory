{-# OPTIONS --without-K --rewriting --experimental-lossy-unification #-}

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
    (iS : is-shape i h t) (iS' : is-shape i h' t')
    (u : h < n) (u' : h' < n)
    → [ i , h' , t' ]≤ₛ[ h , t ]
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
             iS' (empty-shape i) ltS ltS
             (OO[≤ₛ] iS')
          ]ₜ
        ◂$ coeᵀᵐ (![◦] ∙ U[])
        ◂$ el)
      where iS' = shapeₜ↓ iS
  M 1+ O [ i , 1+ h , t ] iS (ltSR ())
  π⋆ᴹ 1+ O [ i , O , t ]→[ .O , .t ] iS iS' ltS ltS done
    = id ◂$ transp-shape (λ ◻ → Sub _ (M 1+ O [ i , O , t ] ◻ ltS)) iS'
  π⋆ᴹ 1+ O [ i , O , .(1+ t') ]→[ .0 , t' ] iS iS' ltS ltS (on-width ltS w)
    = π _ ◂$ transp-shape (λ ◻ → Sub _ (M 1+ O [ i , O , t' ] ◻ ltS)) iS'
  π⋆ᴹ 1+ O [ i , O , 1+ t ]→[ .0 , t' ] iS iS' ltS ltS (on-width (ltSR v) w)
    = π _ ◦ˢᵘᵇ π⋆ᴹ 1+ O [ i , O , 1+ t ]→[ O , 1+ t' ] iS {!!} ltS ltS w
      ◂$ transp-shape (λ ◻ → Sub _ (M 1+ O [ i , O , t' ] ◻ ltS)) {!!}
  π⋆ᴹ 1+ O [ i , 1+ h , t ]→[ h' , t' ] iS iS' (ltSR ()) u' w

  SCT (2+ n) = {!!}
  M 2+ n [ i , h , t ] iS u = {!!}
  π⋆ᴹ 2+ n [ i , h , t ]→[ h' , t' ] iS iS' u u' x = {!!}
