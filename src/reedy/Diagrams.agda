{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

{--- IMPORTANT! This version switches off termination checking temporarily. ---}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I
open import reedy.Cosieves I
open Cosieves-IsStrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr


-- Need this to define the (i, h, t+1) case of the construction.
-- Does this need to be simultaneous with the diagram?
-- case-on-∣ : ∀ {ℓ}
--   → (P : (i h t : ℕ) (s : shape i h t) → Type ℓ)
--   → (i h t : ℕ) (s : shape i h t)
--   → ∀ {j} (f : hom i j)
--   → {u : t < hom-size i h} (d : f ∣ #[ t ] i h u)
--   → (c : f ∣ #[ t ] i h u → ℕ)
--   → (w : ∀ j h → shape j h (c d))
--   → Sub (P i h t s) (P j h (c d) (w (c d)))
-- case-on-∣ = ?


𝔻 : ℕ → Con
Mᵒ : (i h t : ℕ) → shape i h t → Tel (𝔻 (1+ h))

-- Convenience definitions ====

M : (i h t : ℕ) → shape i h t → Con
M i h t s = close (Mᵒ i h t s)

Mᵒᵗᵒᵗ : (i : ℕ) → Tel (𝔻 i)
Mᵒᵗᵒᵗ O = •
Mᵒᵗᵒᵗ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

Mᵒᶠᵘˡˡ : (i h : ℕ) → Tel (𝔻 (1+ h))
Mᵒᶠᵘˡˡ i h = Mᵒ i h full shp
  where
  full = hom-size i h
  shp = full-shape i h

𝔸 : (i : ℕ) → Ty (𝔻 i)
𝔸 i = Πₜₑₗ (Mᵒᵗᵒᵗ i) U

A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒᵗᵒᵗ i [ π (𝔸 i) ]ₜₑₗ)
A i = generic[ Mᵒᵗᵒᵗ i ]type

-- End convenience definitions ====

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f
        sh = count-factors-gives-shape i h t s f
    in Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ i h t s) (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ j h cf sh)

{-# TERMINATING #-}
Mᵒ i h (1+ t) s =
  Mᵒ i h t shp ‣ A h [ {!coercion between equals!} ◦ˢᵘᵇ M⃗ i h t shp (#[ t ] i h u) ]
  where
  shp = prev-shape s
  u : t < hom-size i h
  u = S≤-< s
Mᵒ i (1+ h) O s = Mᵒᶠᵘˡˡ i h [ π (𝔸 (1+ h)) ]ₜₑₗ
Mᵒ i O O s = •

M⃗ i h (1+ t) s {j} f
 with f ∣ #[ t ] i h (S≤-< s)
    | inspect (count-factors i h (1+ t) s) f
    | count-factors i h (1+ t) s f
    | inspect (count-factors i h (1+ t) s) f
    | count-factors-gives-shape i h (1+ t) s f
    | Mᵒ j h (count-factors i h (1+ t) s f) (count-factors-gives-shape i h (1+ t) s f)
    | inspect (uncurry $ Mᵒ j h) (count-factors i h (1+ t) s f , count-factors-gives-shape i h (1+ t) s f)
... | inl x | eq | c | eq' | cs | Mᵒjh | eqq = {!!}
... | inr no | have p | c | have q | cs | Mᵒjh | have idp = {!
  -- ! q ∙ p
  M⃗ i h t prev f!}
    ◦ˢᵘᵇ π (A h [ _ ])
  where
  prev = prev-shape s


--   with
--     count-factors i h (1+ t) s f
--   | inspect (count-factors i h (1+ t) s) f
--   | f ∣ #[ t ] i h (S≤-< s)
--   | inspect (f ∣_) (#[ t ] i h (S≤-< s))
--   | count-factors-gives-shape i h (1+ t) s f
--   | Mᵒ j h (count-factors i h (1+ t) s f) (count-factors-gives-shape i h (1+ t) s f)
--   | inspect (uncurry $ Mᵒ j h) (count-factors i h (1+ t) s f , count-factors-gives-shape i h (1+ t) s f)
-- ... | cf | eqcf | inl (g , p) | eq | cs | Mᵒjhc | eqM = {!!}
-- ... | cf | have q | inr no | have p | cs | Mᵒjhc | eqM = {!q :> (count-factors i h (1+ t) s f == cf)!}
--   -- {!--M⃗ i h t prev f
--   -- p :> (count-factors i h (1+ t) s f == c)
--   -- -- Want : c == count-factors i h t s f!} ◦ˢᵘᵇ π (A h [ _ ])
--   where
--   prev = prev-shape s
--   P = λ ◻ → Sub
--       (𝔻 h ∷ Πₜₑₗ (Mᵒᵗᵒᵗ h) U ++ₜₑₗ Mᵒ i h t (≤-trans (inr ltS) s))
--       (𝔻 h ∷ Πₜₑₗ (Mᵒᵗᵒᵗ h) U ++ₜₑₗ uncurry (Mᵒ j h) ◻)


M⃗ i (1+ h) O s {j} f =
  wkn-sub (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ j h) ({!coercion between equals!} ◦ˢᵘᵇ M⃗ i h full shp f) {!commutation lemma; another component of the definition!} (𝔸 (1+ h))
  where
  full = hom-size i h
  shp = full-shape i h
M⃗ i O O s f = id
