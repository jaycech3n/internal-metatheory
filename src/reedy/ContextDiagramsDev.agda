{-# OPTIONS --without-K --rewriting --termination-depth=4 --allow-unsolved-metas #-}

open import reedy.IndexSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.ContextDiagramsDev {ℓₘᴵ ℓₒ ℓₘ}
  (I : SuitableSemicategory ℓₘᴵ)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SuitableSemicategory I
open import reedy.LinearSievesDev I

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr

SCT : ℕ → Con
𝔸 : (n : ℕ) → Ty (SCT n)
M : (i h t : ℕ) → shape i h t → Tel (SCT (1+ h))

Mᵤ : (Sh : Shape) → Tel (SCT (1+ (height Sh)))
Mᵤ ((i , h , t) , sh) = M i h t sh

M⃗ : (i h t : ℕ) (sh : shape i h t) {j : ℕ} (f : hom i j)
     → Sub (close (M i h t sh)) (close (Mᵤ ([ (i , h , t) , sh ]∙ f)))

SCT O = ◆
SCT (1+ n) = SCT n ∷ 𝔸 n

M[1+_] : ∀ n → Tel (SCT(1+ n))
M[1+ n ] = M (1+ n) n (hom-size (1+ n) n) full-shape[1+ n ]

𝔸 O = U
𝔸 (1+ n) = Πₜₑₗ M[1+ n ] U

A : (n : ℕ) → Tm[ SCT (1+ n) ] (𝔸 n ʷ)
A n = var (SCT (1+ n))

M i O O sh = •
M i (1+ h) O sh = wknₜₑₗ M i h (hom-size i h) (full-level i h) by (𝔸 (1+ h))
M i O (1+ t) sh =
  let M-prev = M i O t (shape↓ sh) -- (1)
  in M-prev ‣ wkn el (A O ᵁ) byₜₑₗ M-prev
M i (1+ h) (1+ t) sh =
  M-prev ‣ el substituted-filler
  where
  M-prev = M i (1+ h) t (shape↓ sh)

  M[1+h]ʷ : Tel (SCT (2+ h))
  M[1+h]ʷ = wknₜₑₗ M[1+ h ] by (𝔸 (1+ h))

  -- Bureaucratic conversion
  p : 𝔸 (1+ h) ʷ == Πₜₑₗ M[1+h]ʷ U
  p = Πₜₑₗ[] M[1+ h ] U (π (𝔸 (1+ h))) ∙ ap (Πₜₑₗ M[1+h]ʷ) U[]

  generic-filler : Tm[ SCT (2+ h) ++ₜₑₗ M[1+h]ʷ ] U
  generic-filler = appₜₑₗ M[1+h]ʷ (coeᵀᵐ p (A (1+ h)))

  substituted-filler : Tm[ SCT (2+ h) ++ₜₑₗ M-prev ] U
  substituted-filler = generic-filler [ {!M⃗ i (1+ h) t (shapeₜ↓ sh)!} ]ₜ ᵁ

M⃗ i h (1+ t) sh f = {!!}
M⃗ i (1+ h) O sh f = {!wkn-sub (M i h (hom-size i h) ?)!}
  -- wkn-sub (M i h (hom-size i h) (full-level i h))
  --         {!Mᵤ ([ (i , h , hom-size i h) , full-level i h ]∙ f)!}
  --         {!M⃗ i h (hom-size i h) (full-level i h) f!}
  --         {!𝔸 (1+ h)!}
M⃗ i O O sh f = id

{- Comments

(1) Putting the definition of M' in a where block causes termination errors?...
-}
