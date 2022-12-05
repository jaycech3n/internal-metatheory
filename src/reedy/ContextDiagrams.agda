{-# OPTIONS --without-K #-}

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
open CwFStructure cwfstr
open PiStructure pistr
open UniverseStructure univstr

SCT : ℕ → Con
M  : (n : ℕ) ((i , h , t) : ℕ³) → is-shape i h t → h < n → Con
M⃗ : (n : ℕ) ((i , h , t) : ℕ³) (iS : is-shape i h t) (u : h < n)
     {m : ℕ} (f : hom i m)
     → Sub (M n (i , h , t) iS u)
           (M n ([ i , h , t ] iS · f)
                (·-is-shape i h t iS f)
                (≤-<-< (height-shape-·' i h t iS f) u))
M= : ∀ n i h t {iS iS'} {u u' : h < n} → M n (i , h , t) iS u == M n (i , h , t) iS' u'
{-
M=~ : ∀ {n} {i h t} {iS : is-shape i h t} {h' t'} {iS' : is-shape i h' t'}
        {u : h < n} {u' : h' < n}
      → {k : ℕ} (e : (h , t) ~⋆ k [ i ] (h' , t'))
      → M n (i , h , t) iS u == M n (i , h' , t') iS' u'
-}

SCT O = ◆
SCT (1+ n) = SCT n ∷ {!!}

{-# TERMINATING #-}
M (1+ n) (i , h , 1+ t) iS u = M (1+ n) (i , h , t) (shapeₜ↓ iS) u ∷ {!var (SCT (1+ n))!}
M (1+ n) (i , 1+ h , O) iS u = M (1+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M (1+ n) (i , O , O) iS u = SCT (1+ n)

M⃗ (1+ n) (i , h , 1+ t) iS u f = {!!}
M⃗ (1+ n) (i , 1+ h , O) iS u {m} f =
  M⃗ (1+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
  ◂$ transp (Sub (M (1+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)))
            (M= (1+ n) m (fst h't') (snd h't'))
  where h't' = shape-· i h (hom-size i h) (shapeₕ↓ iS) f
M⃗ (1+ n) (i , O , O) iS u f = id

M= (1+ n) i h (1+ t)  = {!!}
M= (1+ n) i (1+ h) O = M= (1+ n) i h (hom-size i h)
M= (1+ n) i O O = idp
