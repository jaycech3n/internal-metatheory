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
M : (n : ℕ) ((i , h , t) : ℕ³) → is-shape i h t → h < n → Con
Π′⋆ : ∀ n i h t iS u → Ty (M n (i , h , t) iS u) → Ty (SCT n)
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

-- Minor remark: in the following definitions we have to case split on n > 0, which
-- unfortunately means some code duplication.

SCT (2+ n) = SCT (1+ n) ∷ Π′⋆ (1+ n) (1+ n) n (hom-size (1+ n) n) (full-shape-1+ n) ltS U
SCT (1+ O) = SCT O ∷ U
SCT O = ◆

{-# TERMINATING #-}
M (2+ n) (i , h , 1+ t) iS u = M (2+ n) (i , h , t) (shapeₜ↓ iS) u ∷ {!var (SCT (1+ n))!}
M (2+ n) (i , 1+ h , O) iS u = M (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M (2+ n) (i , O , O) iS u = SCT (2+ n)
M (1+ O) (i , h , 1+ t) iS u =
  M 1 (i , h , t) (shapeₜ↓ iS) u ∷ {!var (SCT 1)!}
M (1+ O) (i , 1+ h , O) iS u = M 1 (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M (1+ O) (i , O , O) iS u = SCT 1

M⃗ (2+ n) (i , h , 1+ t) iS u f = {!!}
M⃗ (2+ n) (i , 1+ h , O) iS u {m} f =
  M⃗ (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
  ◂$ transp (Sub (M (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)))
            (M= (2+ n) m (fst h't') (snd h't'))
  where h't' = shape-· i h (hom-size i h) (shapeₕ↓ iS) f
M⃗ (2+ n) (i , O , O) iS u f = id
M⃗ (1+ O) (i , h , 1+ t) iS u f = {!!}
M⃗ (1+ O) (i , 1+ h , O) iS u {m} f =
  M⃗ 1 (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
  ◂$ transp (Sub (M 1 (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)))
            (M= 1 m (fst h't') (snd h't'))
  where h't' = shape-· i h (hom-size i h) (shapeₕ↓ iS) f
M⃗ (1+ O) (i , O , O) iS u f = id

Π′⋆ (2+ n) i h (1+ t) iS u A = Π′⋆ (2+ n) i h t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (2+ n) i (1+ h) O iS u = Π′⋆ (2+ n) i h (hom-size i h) (shapeₕ↓ iS) (S<-< u)
Π′⋆ (2+ n) i O O iS u A = A
Π′⋆ (1+ O) i h (1+ t) iS u A = Π′⋆ 1 i h t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (1+ O) i (1+ h) O iS u = Π′⋆ 1 i h (hom-size i h) (shapeₕ↓ iS) (S<-< u)
Π′⋆ (1+ O) i O O iS u A = A

M= (2+ n) i h (1+ t) = {!!}
M= (2+ n) i (1+ h) O = M= (2+ n) i h (hom-size i h)
M= (2+ n) i O O = idp
M= (1+ O) i h (1+ t) = {!!}
M= (1+ O) i (1+ h) O = M= 1 i h (hom-size i h)
M= (1+ O) i O O = idp
