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
F : (n : ℕ) → Ty (SCT n)
M : (n : ℕ) ((i , h , t) : ℕ³) → is-shape i h t → h < n → Con
M⃗ : (n : ℕ) ((i , h , t) : ℕ³) (iS : is-shape i h t) (u : h < n)
     {m : ℕ} (f : hom i m)
     {iS· : is-shape-Σ ([ i , h , t ] iS · f)}
     {u· : 2nd ([ i , h , t ] iS · f) < n}
     → Sub (M n (i , h , t) iS u)
           (M n ([ i , h , t ] iS · f) iS· u·)
M= : ∀ n i h t {iS iS'} {u u' : h < n}
     → M n (i , h , t) iS u == M n (i , h , t) iS' u'

Π′⋆ : ∀ n i h t iS u → Ty (M n (i , h , t) iS u) → Ty (SCT n)
π⋆ˢ : ∀ m n → n ≤ m → Sub (SCT m) (SCT n)
π⋆ᴹ : ∀ n i h t iS u iS' u'
      → Sub (M n (i , h , t) iS u) (M n (i , O , O) iS' u')

{-
M=~ : ∀ {n} {i h t} {iS : is-shape i h t} {h' t'} {iS' : is-shape i h' t'}
        {u : h < n} {u' : h' < n}
      → {k : ℕ} (e : (h , t) ~⋆ k [ i ] (h' , t'))
      → M n (i , h , t) iS u == M n (i , h' , t') iS' u'
-}

SCT (1+ n) = SCT n ∷ F n
SCT O = ◆

F O = U
F (1+ n) = Π′⋆ (1+ n) (1+ n) n (hom-size (1+ n) n) (full-shape-1+ n) ltS U

-- How to define this function?...
un-Π′⋆ : ∀ n i h t iS u A
       → Tm[ SCT n ∷ Π′⋆ n i h t iS u A ] ((Π′⋆ n i h t iS u A)ʷ)
       → Tm[ {!!} ] (A [ {!!} ])
un-Π′⋆ n i h t iS u A a = {!!}

M= n i h t {iS} {iS'} {u} {u'} =
  ap2 (M n (i , h , t))
    (prop-path is-shape-is-prop iS iS') (prop-path <-is-prop u u')

{-# TERMINATING #-}
M (1+ n) (i , O , O) iS u = SCT (1+ n)
M (1+ n) (i , O , 1+ t) iS u =
  M (1+ n) (i , O , t) (shapeₜ↓ iS) u
  ∷ (var (SCT 1)
      [ π⋆ˢ (1+ n) 1 (≤-ap-S (O≤ _)) ◦ˢᵘᵇ
        π⋆ᴹ (1+ n) i O t (shapeₜ↓ iS) u (empty-shape i) u
      ]ₜ
    ◂$ coeᵀᵐ (! [◦] ∙ U[])
    ◂$ el)
M (1+ n) (i , 1+ h , 1+ t) iS u =
  M (1+ n) (i , 1+ h , t) (shapeₜ↓ iS) u
  ∷ {!var (SCT (2+ h)) ⦃ idp ⦄ ◂$ un-Π′⋆ (1+ h) (1+ h) h (hom-size (1+ h) h) ? ? U!}
M (2+ n) (i , 1+ h , O) iS u =
  M (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M (1+ O) (i , 1+ h , O) iS (ltSR ())

M⃗ (1+ n) (i , O , O) iS u f = id
M⃗ (1+ n) (i , O , 1+ t) iS u {m} f
 with O <? m | O <? hom-size m O
... | inl O<m | inl O<hom-size =
  {!!}
... | inl O<m | inr O≮hom-size =
  π⋆ᴹ (1+ n) i O (1+ t) iS u (empty-shape i) u
... | inr O≮m | s rewrite ¬O< m O≮m =
  π⋆ᴹ (1+ n) i O (1+ t) iS u (empty-shape i) u
M⃗ (1+ n) (i , 1+ h , 1+ t) iS u f =
  {!!}
M⃗ (2+ n) (i , 1+ h , O) iS u f =
  M⃗ (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
M⃗ (1+ O) (i , 1+ h , O) iS (ltSR ()) f

Π′⋆ (1+ n) i O O iS u A = A
Π′⋆ (1+ n) i O (1+ t) iS u A =
  Π′⋆ (1+ n) i O t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (1+ n) i (1+ h) (1+ t) iS u A =
  Π′⋆ (1+ n) i (1+ h) t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (2+ n) i (1+ h) O iS u A =
  Π′⋆ (2+ n) i h (hom-size i h) (shapeₕ↓ iS) (S<-< u) A
Π′⋆ (1+ O) i (1+ h) O iS (ltSR ()) A

π⋆ˢ m .m (inl idp) = id
π⋆ˢ (2+ m) n (inr (ltSR u)) = π⋆ˢ (1+ m) n (inr u) ◦ˢᵘᵇ π _
π⋆ˢ .(2+ n) (1+ n) (inr ltS) = π _
π⋆ˢ .1 O (inr ltS) = π _

π⋆ᴹ (1+ n) i O O iS u iS' u' = id
π⋆ᴹ (1+ n) i O (1+ t) iS u iS' u' =
  π⋆ᴹ (1+ n) i O t (shapeₜ↓ iS) u iS' u' ◦ˢᵘᵇ π _
π⋆ᴹ (1+ n) i (1+ h) (1+ t) iS u iS' u' =
  π⋆ᴹ (1+ n) i (1+ h) t (shapeₜ↓ iS) u iS' u' ◦ˢᵘᵇ π _
π⋆ᴹ (2+ n) i (1+ h) O iS u iS' u' =
  π⋆ᴹ (2+ n) i h (hom-size i h) (shapeₕ↓ iS) (S<-< u) iS' u'
π⋆ᴹ (1+ O) i (1+ h) O iS (ltSR ())

{-
{-# TERMINATING #-}
M (2+ n) (i , 1+ h , 1+ t) iS u =
  M (2+ n) (i , 1+ h , t) (shapeₜ↓ iS) u ∷ {!var (SCT (1+ n))!}
M (2+ n) (i , O , 1+ t) iS u =
  M (2+ n) (i , O , t) (shapeₜ↓ iS) u ∷ {!var (SCT (1+ n))!}
M (2+ n) (i , 1+ h , O) iS u = M (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)
M (2+ n) (i , O , O) iS u = SCT (2+ n)

M (1+ O) (i , .O , 1+ t) iS ltS =
  M 1 (i , O , t) (shapeₜ↓ iS) ltS
  ∷ (var (SCT 1) [ π⋆ 1 i t (empty-shape i) ltS ]ₜ
    ◂$ coeᵀᵐ (! [◦] ∙ U[])
    ◂$ el)
M (1+ O) (i , 1+ h , O) iS (ltSR ())
M (1+ O) (i , O , O) iS u = SCT 1

M⃗ (2+ n) (i , h , 1+ t) iS u f = {!!}
M⃗ (2+ n) (i , 1+ h , O) iS u {m} f =
  M⃗ (2+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f
M⃗ (2+ n) (i , O , O) iS u f = id
M⃗ (1+ O) (i , .O , 1+ t) iS ltS {m} f with O <? m | O <? hom-size m O
... | inl O<m | inl O<hom-size = {!!}
... | inl O<m | inr O≮hom-size = π⋆ 1 i (1+ t) {iS} {ltS} (empty-shape i) ltS
... | inr O≮m | _ rewrite ¬O< m O≮m = π⋆ 1 i (1+ t) {iS} {ltS} (empty-shape i) ltS
M⃗ (1+ O) (i , O , O) iS u f = id
M⃗ (1+ O) (i , 1+ _ , O) iS (ltSR ()) {m} f

M= n i h t {iS} {iS'} {u} {u'} =
  ap2 (M n (i , h , t)) (prop-path is-shape-is-prop iS iS') (prop-path <-is-prop u u')

Π′⋆ (2+ n) i (1+ h) (1+ t) iS u A = Π′⋆ (2+ n) i (1+ h) t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (2+ n) i O (1+ t) iS u A = Π′⋆ (2+ n) i O t (shapeₜ↓ iS) u (Π′ _ A)
Π′⋆ (2+ n) i (1+ h) O iS u = Π′⋆ (2+ n) i h (hom-size i h) (shapeₕ↓ iS) (S<-< u)
Π′⋆ (2+ n) i O O iS u A = A
Π′⋆ (1+ O) i .O (1+ t) iS ltS A = Π′⋆ 1 i O t (shapeₜ↓ iS) ltS (Π′ _ A)
Π′⋆ (1+ O) i O O iS u A = A
Π′⋆ (1+ O) i (1+ h) O iS (ltSR ())

π⋆ n i O _ _ = id ◂$ coe-cod (M= n i O O)
π⋆ (2+ n) i (1+ t) iS u = π⋆ (2+ n) i t (empty-shape i) u ◦ˢᵘᵇ (π _)
π⋆ (1+ O) i (1+ t) {u₀ = ltS} iS u = π⋆ 1 i t iS u ◦ˢᵘᵇ (π _)
-}
