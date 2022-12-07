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
open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr

SCT : ℕ → Con
M : (n : ℕ) ((i , h , t) : ℕ³) → is-shape i h t → h < n → Con
M⃗ : (n : ℕ) ((i , h , t) : ℕ³) (iS : is-shape i h t) (u : h < n)
     {m : ℕ} (f : hom i m)
     {iS· : is-shape-Σ ([ i , h , t ] iS · f)}
     {u· : 2nd ([ i , h , t ] iS · f) < n}
     → Sub (M n (i , h , t) iS u)
           (M n ([ i , h , t ] iS · f) iS· u·)
M= : ∀ n i h t {iS iS'} {u u' : h < n} → M n (i , h , t) iS u == M n (i , h , t) iS' u'

Π′⋆ : ∀ n i h t iS u → Ty (M n (i , h , t) iS u) → Ty (SCT n)
π⋆ : ∀ n i t {iS₀} {u₀} iS u → Sub (M n (i , O , t) iS₀ u₀) (M n (i , O , O) iS u)

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
M (2+ n) (i , h , 1+ t) iS u =
  M (2+ n) (i , h , t) (shapeₜ↓ iS) u ∷ {!var (SCT (1+ n))!}
M (2+ n) (i , 1+ h , O) iS u = M (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M (2+ n) (i , O , O) iS u = SCT (2+ n)
M (1+ O) (i , O , O) iS u = SCT 1
M (1+ O) (i , .O , 1+ t) iS ltS =
  M 1 (i , O , t) (shapeₜ↓ iS) ltS
  ∷ (var (SCT 1) [ π⋆ 1 i t (empty-shape i) ltS ]ₜ
    ◂$ coeᵀᵐ (! [◦] ∙ U[])
    ◂$ el)
M (1+ O) (i , 1+ _ , O) iS (ltSR ())

M⃗ (2+ n) (i , h , 1+ t) iS u f = {!!}
M⃗ (2+ n) (i , 1+ h , O) iS u {m} f =
  M⃗ (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
M⃗ (2+ n) (i , O , O) iS u f = id
M⃗ (1+ O) (i , .O , 1+ t) iS ltS {m} f with O <? m
... | inr O≮m rewrite ¬O< m O≮m = π⋆ 1 i (1+ t) {iS} {ltS} (empty-shape i) ltS
... | inl O<m
      with O <? hom-size m O
...   | inl O<hom-size = {!!}
...   | inr O≮hom-size = π⋆ 1 i (1+ t) {iS} {ltS} (empty-shape i) ltS
M⃗ (1+ O) (i , O , O) iS u f = id
M⃗ (1+ O) (i , 1+ _ , O) iS (ltSR ()) {m} f

M= n i h t {iS} {iS'} {u} {u'} =
  ap2 (M n (i , h , t)) (prop-path is-shape-is-prop iS iS') (prop-path <-is-prop u u')

Π′⋆ (2+ n) i h (1+ t) iS u A = Π′⋆ (2+ n) i h t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (2+ n) i (1+ h) O iS u = Π′⋆ (2+ n) i h (hom-size i h) (shapeₕ↓ iS) (S<-< u)
Π′⋆ (2+ n) i O O iS u A = A
Π′⋆ (1+ O) i .O (1+ t) iS ltS A = Π′⋆ 1 i O t (shapeₜ↓ iS) ltS (Π′ _ A)
Π′⋆ (1+ O) i O O iS u A = A
Π′⋆ (1+ O) i (1+ h) O iS (ltSR ())

π⋆ n i O _ _ = id ◂$ coe-cod (M= n i O O)
π⋆ (2+ n) i (1+ t) iS u = π⋆ (2+ n) i t (empty-shape i) u ◦ˢᵘᵇ (π _)
π⋆ (1+ O) i (1+ t) {u₀ = ltS} iS u = π⋆ 1 i t iS u ◦ˢᵘᵇ (π _)
