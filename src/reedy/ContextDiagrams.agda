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
M= : ∀ {n} i h t {iS iS'} {u u'} → M n (i , h , t) iS u == M n (i , h , t) iS' u'
{-
M=~ : ∀ {n} {i h t} {iS : is-shape i h t} {h' t'} {iS' : is-shape i h' t'}
        {u : h < n} {u' : h' < n}
      → {k : ℕ} (e : (h , t) ~⋆ k [ i ] (h' , t'))
      → M n (i , h , t) iS u == M n (i , h' , t') iS' u'
-}

SCT O = ◆
SCT (1+ n) = SCT n ∷ {!!}

{-# TERMINATING #-}
M n (i , h , 1+ t) iS u = M n (i , h , t) (shapeₜ↓ iS) u ∷ {!!}
M n (i , 1+ h , O) iS u = M n (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M n (i , O , O) iS u = SCT n

M⃗ n (i , h , 1+ t) iS u f = {!!}
M⃗ n (i , 1+ h , O) iS u {m} f =
  M⃗ n (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
  ◂$ transp (Sub (M n (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)))
            (M= m (fst h't') (snd h't'))
  where h't' = shape-· i h (hom-size i h) (shapeₕ↓ iS) f
M⃗ n (i , O , O) iS u f = id

M= i h (1+ t)  = {!!}
M= i (1+ h) O = M= i h (hom-size i h)
M= i O O = idp
