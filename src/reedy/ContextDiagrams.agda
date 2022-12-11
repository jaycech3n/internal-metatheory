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

π⋆ᴹ : ∀ n i {h t h' t'} iS iS' u u' -- projection from larger to smaller matching context
      → (h' , t') ≤ₛ (h , t)
      → Sub (M n (i , h , t) iS u) (M n (i , h' , t') iS' u')
Π′⋆ : ∀ n i h t iS u → Ty (M n (i , h , t) iS u) → Ty (SCT n)

{-
M= : ∀ n i h t {iS iS'} {u u' : h < n}
     → M n (i , h , t) iS u == M n (i , h , t) iS' u'

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

π⋆ˢ : ∀ m n → n ≤ m → Sub (SCT m) (SCT n)
π⋆ˢ m .m (inl idp) = id
π⋆ˢ .(1+ n) n (inr ltS) = π (F n)
π⋆ˢ (2+ m) n (inr (ltSR u)) = π⋆ˢ (1+ m) n (inr u) ◦ˢᵘᵇ π _

π⋆ᴹ₀ : ∀ n i h t iS u u'
      → Sub (M n (i , h , t) iS u) (M n (i , O , O) (empty-shape i) u')
π⋆ᴹ₀ n i h t iS u u' = π⋆ᴹ n i iS (empty-shape i) u u' (OO≤ₛ h t)

{-# TERMINATING #-}
M (1+ n) (i , O , O) iS u = SCT (1+ n)
M (1+ n) (i , O , 1+ t) iS u =
  M (1+ n) (i , O , t) (shapeₜ↓ iS) u
  ∷ (var (SCT 1)
      [ π⋆ˢ (1+ n) 1 (≤-ap-S (O≤ _)) ◦ˢᵘᵇ
        π⋆ᴹ₀ (1+ n) i O t (shapeₜ↓ iS) u u
      ]ₜ
    ◂$ coeᵀᵐ (! [◦] ∙ U[])
    ◂$ el)
M (1+ n) (i , 1+ h , 1+ t) iS u =
  M (1+ n) (i , 1+ h , t) (shapeₜ↓ iS) u
  ∷ {!var (SCT (2+ h)) ⦃ idp ⦄ ◂$ un-Π′⋆ (1+ h) (1+ h) h (hom-size (1+ h) h) ? ? U!}
M (1+ n) (i , 1+ h , O) iS u =
  M (1+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u)


M⃗ (1+ n) (i , O , O) iS u f = id
M⃗ (1+ n) (i , O , 1+ t) iS u {m} f
 with O <? m | O <? hom-size m O
... | inl O<m | inl O<hom-size = {!!}
... | inl O<m | inr O≮hom-size = π⋆ᴹ₀ (1+ n) i O (1+ t) iS u u
... | inr O≮m | s rewrite ¬O< m O≮m = π⋆ᴹ₀ (1+ n) i O (1+ t) iS u u
M⃗ (1+ n) (i , 1+ h , 1+ t) iS u f = {!!}
M⃗ (1+ n) (i , 1+ h , O) iS u f =
  M⃗ (1+ n) (i , h , hom-size i h) (shapeₕ↓ iS) (S<-< u) f



π⋆ᴹ (1+ n) i {.(1+ h')} {O} {h'} {t'} iS iS' u u' (inl ltS) = {!!}
π⋆ᴹ (1+ n) i {.(1+ h')} {1+ t} {h'} {t'} iS iS' u u' (inl ltS) = {!!}

π⋆ᴹ (1+ n) i iS iS' u u' (inl (ltSR v)) = {!!}

π⋆ᴹ (1+ n) i iS iS' u u' (inr (idp , inl idp))
  rewrite shape= iS iS' | <= u u' = id

π⋆ᴹ (1+ n) i {O} {.(1+ t')} {.O} {t'} iS iS' u u' (inr (idp , inr ltS))
  rewrite shape= iS' (shapeₜ↓ iS) | <= u' u = π _
π⋆ᴹ (1+ n) i {1+ h} {.(1+ t')} {.(1+ h)} {t'} iS iS' u u' (inr (idp , inr ltS))
  rewrite shape= iS' (shapeₜ↓ iS) | <= u' u = π _

π⋆ᴹ (1+ n) i {O} {1+ t} {.O} {t'} iS iS' u u' (inr (idp , inr (ltSR v)))
  rewrite shape= iS' (shapeₜ↓ (shapeₜ< (<-ap-S v) iS))
  = (π _) ◦ˢᵘᵇ
    π⋆ᴹ (1+ n) i iS (shapeₜ< (<-ap-S v) iS) u u' (≤ₛ-by-width (≤-ap-S (inr v)))

π⋆ᴹ (1+ n) i {1+ h} {1+ t} {.(1+ h)} {t'} iS iS' u u' (inr (idp , inr (ltSR v))) = {!!}

Π′⋆ (1+ n) i h t iS u = Π′⋆-aux h t O O iS (empty-shape i) u (O<S n) (OO≤ₛ h t)
  where
  Π′⋆-aux : ∀ h t h' t' iS iS' u u'
    → (h' , t') ≤ₛ (h , t)
    → Ty (M (1+ n) (i , h , t) iS u)
    → Ty (M (1+ n) (i , h' , t') iS' u')

  Π′⋆-aux h t .h .t iS iS' u u' (inr (idp , inl idp)) A
    rewrite shape= iS iS' | <= u u' = A

  Π′⋆-aux (1+ h) t h' t' iS iS' u u' (inl (ltSR v)) A = {!!}

  Π′⋆-aux .(1+ h') O h' t' iS iS' u u' (inl ltS) A =
    Π′⋆-aux h' (hom-size i h') h' t'
      (full-level i h' (S≤-≤ (hcond iS))) iS' (S<-< u) u'
      (≤ₛ-by-width (tcond iS')) A
  Π′⋆-aux .(1+ h') (1+ t) h' .(hom-size i h') iS iS'@(shape-conds hcond (inl idp)) u u' (inl ltS) A = {!!}
  Π′⋆-aux .(1+ h') (1+ t) h' t' iS (shape-conds hcond (inr v)) u u' (inl ltS) A = {!!}

  Π′⋆-aux O .(1+ t') .O t' iS iS' u u' (inr (idp , inr ltS)) A
    rewrite shape= iS' (shapeₜ↓ iS) | <= u' u
    = Π′ _ A
  Π′⋆-aux (1+ h) .(1+ t') .(1+ h) t' iS iS' u u' (inr (idp , inr ltS)) A
    rewrite shape= iS' (shapeₜ↓ iS) | <= u' u
    = Π′ _ A

  Π′⋆-aux O (1+ t) .O t' iS iS' u u' (inr (idp , inr (ltSR v))) A
    rewrite shape= iS' (shapeₜ↓ (shapeₜ< (<-ap-S v) iS))
    = Π′ _
        (Π′⋆-aux O (1+ t) O (1+ t')
          iS (shapeₜ< (<-ap-S v) iS) u u'
          (≤ₛ-by-width (≤-ap-S (inr v))) A)
  Π′⋆-aux (1+ h) (1+ t) .(1+ h) t' iS iS' u u' (inr (idp , inr (ltSR v))) A
    rewrite shape= iS' (shapeₜ↓ (shapeₜ< (<-ap-S v) iS))
    = Π′ _
        (Π′⋆-aux (1+ h) (1+ t) (1+ h) (1+ t')
          iS (shapeₜ< (<-ap-S v) iS) u u'
          (≤ₛ-by-width (≤-ap-S (inr v))) A)

{-
π⋆ᴹ (1+ n) i O O iS u iS' u' = id
π⋆ᴹ (1+ n) i O (1+ t) iS u iS' u' =
  π⋆ᴹ (1+ n) i O t (shapeₜ↓ iS) u iS' u' ◦ˢᵘᵇ π _
π⋆ᴹ (1+ n) i (1+ h) (1+ t) iS u iS' u' =
  π⋆ᴹ (1+ n) i (1+ h) t (shapeₜ↓ iS) u iS' u' ◦ˢᵘᵇ π _
π⋆ᴹ (2+ n) i (1+ h) O iS u iS' u' =
  π⋆ᴹ (2+ n) i h (hom-size i h) (shapeₕ↓ iS) (S<-< u) iS' u'
π⋆ᴹ (1+ O) i (1+ h) O iS (ltSR ())
-}

{-
M= n i h t {iS} {iS'} {u} {u'} =
  ap2 (M n (i , h , t))
    (prop-path is-shape-is-prop iS iS') (prop-path <-is-prop u u')
-}
