{-# OPTIONS --without-K --rewriting #-}

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

SCT : ℕ → Con
F : (n : ℕ) → Ty (SCT n)
M_[_,_,_] : (n i h t : ℕ) → is-shape i h t → h < n → Con
M⃗_[_,_,_] :
  (n i h t : ℕ) (iS : is-shape i h t) (u : h < n)
  {m : ℕ} (f : hom i m)
  {iS· : is-shape-Σ ([ i , h , t ] iS · f)}
  {u· : 2nd ([ i , h , t ] iS · f) < n}
  → let s = [ i , h , t ] iS · f in
    Sub (M n [ i , h , t ] iS u)
        (M n [ fst s , 2nd s , 3rd s ] iS· u·)

Π′⋆_[_,_,_]→[_,_] : ∀ n i h t h' t' iS u iS' u'
  → [ i , h' , t' ]≤ₛ[ h , t ]
  → Ty (M n [ i , h , t ] iS u) → Ty (M n [ i , h' , t' ] iS' u')

π⋆ᴹ : ∀ n i {h t h' t'} iS iS' u u' -- projection from larger to smaller matching context
  → [ i , h' , t' ]≤ₛ[ h , t ]
  → Sub (M n [ i , h , t ] iS u) (M n [ i , h' , t' ] iS' u')

SCT O = ◆
SCT (1+ n) = SCT n ∷ F n

M n [ i , O , O ] iS u = SCT n
M n [ i , O , 1+ t ] iS u = M n [ i , O , t ] (shapeₜ↓ iS) u ∷ {!!}
M n [ i , 1+ h , O ] iS u = M n [ i , h , hom-size i h ] (shapeₕ↓ iS) (S<-< u)
M n [ i , 1+ h , 1+ t ] iS u = M n [ i , 1+ h , t ] (shapeₜ↓ iS) u ∷ {!!}

M⃗ n [ i , h , t ] iS u f = {!!}

Π′⋆ n [ i , h , t ]→[ .h , .t ] iS u iS' u' done A
  rewrite shape= iS' iS | <= u' u = A
Π′⋆ n [ i , O , t ]→[ .O , t' ] iS u iS' u' (on-width v w) A
  rewrite shape= iS' (shapeₜ↓ $ shape-conds (hcond iS') (≤-trans (<-S≤ v) (tcond iS)))
  = Π′ _ (Π′⋆ n [ i , O , t ]→[ O , 1+ t' ] iS u iS'' u' w A)
    where
    iS'' : is-shape i O (1+ t')
    iS'' = shape-conds (hcond iS') (≤-trans (<-S≤ v) (tcond iS))
Π′⋆ n [ i , 1+ h , t ]→[ .(1+ h) , t' ] iS u iS' u' (on-width v w) A
  rewrite shape= iS' (shapeₜ↓ $ shape-conds (hcond iS') (≤-trans (<-S≤ v) (tcond iS)))
  = Π′ _ (Π′⋆ n [ i , 1+ h , t ]→[ 1+ h , 1+ t' ] iS u iS'' u' w A)
    where
    iS'' : is-shape i (1+ h) (1+ t')
    iS'' = shape-conds (hcond iS') (≤-trans (<-S≤ v) (tcond iS))
Π′⋆ n [ i , h , t ]→[ h' , .(hom-size i h') ] iS u iS' u' (on-height-width-max v w) A
  rewrite shape= iS' (shapeₕ↓ (new-level i (1+ h') (≤-trans (<-S≤ v) (hcond iS))))
        | <= u' (S<-< (≤-<-< (<-S≤ v) u))
  = Π′⋆ n [ i , h , t ]→[ 1+ h' , O ] iS u iS'' v' w A
    where
    iS'' : is-shape i (1+ h') O
    iS'' = new-level i (1+ h') (≤-trans (<-S≤ v) (hcond iS))
    v' : 1+ h' < n
    v' = ≤-<-< (<-S≤ v) u
Π′⋆ n [ i , h , t ]→[ O , t' ] iS u iS' u' (on-height-width<max v v' w) A
  rewrite shape= iS' (shapeₜ↓ $ shape-conds (hcond iS') (<-S≤ v'))
  = Π′ _ (Π′⋆ n [ i , h , t ]→[ O , 1+ t' ] iS u iS'' u' w A)
    where
    iS'' : is-shape i O (1+ t')
    iS'' = shape-conds (hcond iS') (<-S≤ v')
Π′⋆ n [ i , h , t ]→[ 1+ h' , t' ] iS u iS' u' (on-height-width<max v v' w) A
  rewrite shape= iS' (shapeₜ↓ $ shape-conds (hcond iS') (<-S≤ v'))
  = Π′ _ (Π′⋆ n [ i , h , t ]→[ 1+ h' , 1+ t' ] iS u iS'' u' w A)
    where
    iS'' : is-shape i (1+ h') (1+ t')
    iS'' = shape-conds (hcond iS') (<-S≤ v')

π⋆ᴹ n i iS iS' u u' w = {!!}

F O = U
F (1+ n) =
  Π′⋆ (1+ n) [ 1+ n , n , hom-size (1+ n) n ]→[ O , O ]
    (full-shape-1+ n) ltS (empty-shape (1+ n)) (O<S n)
    (≤ₛ-ind (full-shape-1+ n) (empty-shape (1+ n)) OO≤ₛ) U
