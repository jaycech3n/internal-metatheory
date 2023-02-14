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
  M[_,_,_],F : (i h t n : ℕ) → is-shape i h t → h < n → Σ[ Γ ː Con ] Ty Γ

  M_[_,_,_] : (n i h t : ℕ) → is-shape i h t → h < n → Con
  M n [ i , h , t ] iS u = fst (M[ i , h , t ],F n iS u)

  SCT : ℕ → Con
  SCT O = ◆
  SCT (1+ n) = M (1+ n) [ 1+ n , O , O ] iS u
    where
    iS = empty-shape (1+ n)
    u = O<S n

  -- Projection from larger to smaller matching context drops components
  π⋆ᴹ_[_,_,_]→[_,_] :
    (n i h t h' t' : ℕ)
    (iS : is-shape i h t) (iS' : is-shape i h' t')
    (u : h < n) (u' : h' < n)
    → (h' , t') ≤ₛ (h , t)
    → Sub (M n [ i , h , t ] iS u) (M n [ i , h' , t' ] iS' u')

  {- M⃗_[_,_,_] :
    (n i h t : ℕ) (iS : is-shape i h t) (u : h < n)
    {m : ℕ} (f : hom i m)
    {iS· : is-shape-Σ ([ i , h , t ] iS · f)}
    {u· : 2nd ([ i , h , t ] iS · f) < n}
    → let s = [ i , h , t ] iS · f in
      Sub (M n [ i , h , t ] iS u)
          (M n [ fst s , 2nd s , 3rd s ] iS· u·) -}
  Π′⋆_[_,_,_]→[_,_] :
    (n i h t h' t' : ℕ)
    (iS : is-shape i h t) (iS' : is-shape i h' t')
    (u : h < n) (u' : h' < n)
    → (h' , t') ≤ₛ (h , t)
    → Ty (M n [ i , h , t ] iS u) → Ty (M n [ i , h' , t' ] iS' u')
  -- Drops higher dimensional fillers
  -- π⋆ˢ : ∀ n h → h < n → Sub (SCT n) (SCT h)

  F : (n : ℕ) → Ty (SCT n)
  F O = U
  F (1+ n) =
    Π′⋆ (1+ n) [ 1+ n , n , hom-size (1+ n) n ]→[ O , O ] iS iS' u u' w
    $ U -- (snd (M[ 1+ n , n , hom-size (1+ n) n ],F (1+ n) iS ltS))
    where
    iS = full-shape-1+ n
    iS' = empty-shape (1+ n)
    u = ltS
    u' = O<S n
    w = O≤ₛ n (hom-size (1+ n) n)

  M[ i , h , 1+ t ],F (1+ n) iS u =
    (M (1+ n) [ i , h , t ] iS' u ∷ {!!})
    , U
    where
    iS' = shapeₜ↓ iS
  M[ i , 1+ h , O ],F (1+ n) iS u =
    M[ i , h , hom-size i h ],F (1+ n) iS' u'
    where
    iS' = shapeₕ↓ iS
    u' = S<-< u
  M[ i , O , O ],F (1+ n) iS u = (SCT n ∷ F n) , U

  π⋆ᴹ (1+ n) [ i , h , t ]→[ h' , t' ] iS iS' u u' w = {!!}

  -- M⃗ (1+ n) [ i , h , t ] = {!!}

  Π′⋆ (1+ n) [ i , h , t ]→[ h' , t' ] iS iS' u u' w = {!!}

  -- π⋆ˢ (1+ n) h u = {!!}
