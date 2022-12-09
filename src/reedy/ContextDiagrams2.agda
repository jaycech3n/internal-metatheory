{-- Remark on this file:

To define the "un-Π" function that's inverse to Π′⋆, we need that (Π′⋆ A) is a Π in
some form. The definition of Π′⋆ in reedy.ContextDiagrams.agda does not satisfy this
definitionally.

In this version of the file, we try to use decidability of `is-shape` and `<` together
with with-abstraction to avoid transports when defining the necessary auxiliary
functions.  -}

{-# OPTIONS --without-K #-}

open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import reedy.IndexSemicategories

module reedy.ContextDiagrams2 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open import reedy.LinearSieves2 I
open SuitableSemicategory I
open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr

SCT : ℕ → Con
F : (n : ℕ) → Ty (SCT n)
M : (n : ℕ) ((i , h , t) : ℕ³)
    (iS : True (is-shape? i h t)) (u : True (h <? n))
    → Con
M⃗ : (n : ℕ) ((i , h , t) : ℕ³)
     (iS : True (is-shape? i h t)) (u : True (h <? n))
     {m : ℕ} (f : hom i m)
     {iS· : True (is-shape-Σ? ([ i , h , t ] iS · f))}
     {u· : True (2nd ([ i , h , t ] iS · f) <? n)}
     → Sub (M n (i , h , t) iS u)
           (M n ([ i , h , t ] iS · f) iS· u·)

Π′⋆ : ∀ n i h t iS u → Ty (M n (i , h , t) iS u) → Ty (SCT n)
π⋆ˢ : ∀ m n → n ≤ m → Sub (SCT m) (SCT n)
π⋆ᴹ : ∀ n i h t h' t'
      → (h' , t') ≤ₛ (h , t)
      → {iS : True (is-shape? i h t)} {iS' : True (is-shape? i h' t')}
      → {u : True (h <? n)} {u' : True (h' <? n)}
      → Sub (M n (i , h , t) iS u) (M n (i , h' , t') iS' u')

SCT (1+ n) = SCT n ∷ F n
SCT O = ◆

F O = U
F (1+ n) = Π′⋆ (1+ n) (1+ n) n (hom-size (1+ n) n) (by $ full-shape-1+ n) (by ltS) U

{-# TERMINATING #-}
M (1+ n) (i , O , O) iS u = SCT (1+ n)
M (1+ n) (i , O , 1+ t) iS u =
  M (1+ n) (i , O , t) (by $ shapeₜ↓ ⌜ iS ⌝) u
  ∷ (var (SCT 1) [
      π⋆ˢ (1+ n) 1 (≤-ap-S (O≤ n)) ◦ˢᵘᵇ
      π⋆ᴹ (1+ n) i O t O O (OO≤ₛ O t)
    ]ₜ
    ◂$ coeᵀᵐ (! [◦] ∙ U[])
    ◂$ el)
M (2+ n) (i , 1+ h , 1+ t) iS u =
  M (2+ n) (i , 1+ h , t) (by $ shapeₜ↓ ⌜ iS ⌝) u
  ∷ {!!}
M (2+ n) (i , 1+ h , O) iS u =
  M (2+ n) (i , h , hom-size i h) (by $ shapeₕ↓ ⌜ iS ⌝) (by $ S<-< ⌜ u ⌝)

M⃗ (1+ n) (i , O , O) iS u f = id
M⃗ (1+ n) (i , O , 1+ t) iS u f = {!!}
M⃗ (2+ n) (i , 1+ h , 1+ t) iS u f = {!!}
M⃗ (2+ n) (i , 1+ h , O) iS u {m} f {iS·} {u·} =
  M⃗ (2+ n) (i , h , hom-size i h) (by $ shapeₕ↓ ⌜ iS ⌝) (by $ S<-< ⌜ u ⌝) f

Π′⋆ (1+ n) i h t iS u A = {!!}

π⋆ˢ m .m (inl idp) = id
π⋆ˢ .(1+ n) n (inr ltS) = π (F n)
π⋆ˢ (1+ m) n (inr (ltSR u)) = π⋆ˢ m n (inr u) ◦ˢᵘᵇ π (F m)

π⋆ᴹ (1+ n) i .(1+ h') t h' t' (inl ltS) = {!!}
π⋆ᴹ (1+ n) i .(1+ _) t h' t' (inl (ltSR x)) = {!!}
π⋆ᴹ (1+ n) i h .(1+ t') .h t' (inr (idp , inr ltS)) = {!!}
π⋆ᴹ (1+ n) i h .(1+ _) .h t' (inr (idp , inr (ltSR x))) = {!!}
π⋆ᴹ (1+ n) i O O .O .O (inr (idp , inl idp)) {iS} {iS'} {u} {u'} = id
π⋆ᴹ (1+ n) i O (1+ t) .O .(1+ t) (inr (idp , inl idp)) {iS} {iS'} {u} {u'}
 with is-shape? i O (1+ t) | iS | iS'
    | M (1+ n) (i , O , 1+ t) iS u | M (1+ n) (i , O , 1+ t) iS' u'
    | inspect (M (1+ n) (i , O , 1+ t) iS) u
    | inspect (M (1+ n) (i , O , 1+ t) iS') u'
... | inl yes | tt | tt | M | M' | have idp | have idp = id
π⋆ᴹ (2+ n) i (1+ h) (1+ t) .(1+ h) .(1+ t) (inr (idp , inl idp)) {iS} {iS'} {u} {u'} = {!!}
{- with is-shape? i (1+ h) (1+ t) | iS | iS' | 1+ h <? 2+ n | u | u'
    | M (2+ n) (i , 1+ h , 1+ t) iS u | M (2+ n) (i , 1+ h , 1+ t) iS' u'
    | inspect (M (2+ n) (i , 1+ h , 1+ t) iS) u
    | inspect (M (2+ n) (i , 1+ h , 1+ t) iS') u'
... | s? | s | s' | h? | v | v' | M | M' | ins | ins' = {!!}-}
π⋆ᴹ (2+ n) i (1+ h) O .(1+ h) .O (inr (idp , inl idp)) {iS} {iS'} {u} {u'}
 with is-shape? i (1+ h) O | iS | iS' | 1+ h <? 2+ n | u | u'
    | M (2+ n) (i , 1+ h , O) iS u | M (2+ n) (i , 1+ h , O) iS' u'
    | inspect (M (2+ n) (i , 1+ h , O) iS) u
    | inspect (M (2+ n) (i , 1+ h , O) iS') u'
... | inl _ | tt | tt | inl _ | tt | tt | M | M' | have idp | have idp = id
