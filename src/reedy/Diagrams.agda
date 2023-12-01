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


-- Also use this equation
M=₁ : ∀ i h t (s : shape i h (1+ t))
      → let prev = prev-shape s
            u = S≤-< s
            [t] = #[ t ] i h u
            cf = count-factors i h t prev [t]
            sh = count-factors-gives-shape i h t prev [t]
        in M h h cf sh == close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)


{-# TERMINATING #-}
Mᵒ i h (1+ t) s =
  Mᵒ i h t shp ‣ A h [ idd eq ◦ˢᵘᵇ M⃗ i h t shp (#[ t ] i h u) ]
  where
  shp = prev-shape s
  u : t < hom-size i h
  u = S≤-< s

  c = count-factors i h t shp (#[ t ] i h u)
  cs = count-factors-gives-shape i h t shp (#[ t ] i h u)

  eq : M h h c cs == (𝔻 (1+ h) ++ₜₑₗ Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)
  eq = M=₁ i h t s

Mᵒ i (1+ h) O s = Mᵒᶠᵘˡˡ i h [ π (𝔸 (1+ h)) ]ₜₑₗ
Mᵒ i O O s = •


M=₁ i O t s =
  M O O cf sh =⟨ ap (uncurry $ M O O) (pair= p {b' = O≤ _} (from-transp _ _ shape-path)) ⟩
  M O O O (O≤ (hom-size O O)) =⟨ idp ⟩
  close (Mᵒᵗᵒᵗ O [ π (𝔸 O) ]ₜₑₗ) =∎
  where
  prev = prev-shape s
  u = S≤-< s
  [t] = #[ t ] i O u
  cf = count-factors i O t prev [t]
  sh = count-factors-gives-shape i O t prev [t]

  p : cf == O
  p = count-factors-top-level i O t prev [t]

M=₁ i (1+ h) t s =
  M (1+ h) (1+ h) cf sh
    =⟨ ap (uncurry $ M (1+ h) (1+ h))
          (pair= p {b' = O≤ _} (from-transp _ _ shape-path)) ⟩
  M (1+ h) (1+ h) O (O≤ _) =⟨ idp ⟩
  close (Mᵒᵗᵒᵗ (1+ h) [ π (𝔸 (1+ h)) ]ₜₑₗ) =∎
  where
  prev = prev-shape s
  u = S≤-< s
  [t] = #[ t ] i (1+ h) u
  cf = count-factors i (1+ h) t prev [t]
  sh = count-factors-gives-shape i (1+ h) t prev [t]

  p : cf == O
  p = count-factors-top-level i (1+ h) t prev [t]

M⃗ i h (1+ t) s {j} f
 with f ∣ #[ t ] i h (S≤-< s)
    | inspect (count-factors i h (1+ t) s) f
    | count-factors i h (1+ t) s f
    | inspect (count-factors i h (1+ t) s) f
    | count-factors-gives-shape i h (1+ t) s f
    | Mᵒ j h (count-factors i h (1+ t) s f)
        (count-factors-gives-shape i h (1+ t) s f)
    | inspect (uncurry $ Mᵒ j h)
        (count-factors i h (1+ t) s f
        , count-factors-gives-shape i h (1+ t) s f)

... | inl x | eq | c | eq' | cs | Mᵒjh | eqq = {!!}

... | inr no | have p | c | have q | cs | Mᵒjh | have idp =
  idd eq ◦ˢᵘᵇ M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ])
  where
  prev = prev-shape s

  cf = count-factors i h t prev f
  cfs = count-factors-gives-shape i h t prev f

  eq : M j h cf cfs == M j h c cs
  eq = ap (uncurry $ M j h) (pair= (! p ∙ q) (from-transp _ _ shape-path))

M⃗ i (1+ h) O s {j} f =
  wkn-sub (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ j h)
    (idd eq ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f)
    {!commutation lemma; another component of the definition!}
    (𝔸 (1+ h))
  where
  fullᵢ = hom-size i h
  shpᵢ = full-shape i h

  cf = count-factors i h fullᵢ shpᵢ f
  sh = count-factors-gives-shape i h fullᵢ shpᵢ f

  fullⱼ = hom-size j h
  shpⱼ = full-shape j h

  eq : M j h cf sh == M j h fullⱼ shpⱼ
  eq = ap (uncurry $ M j h)
          (pair= (count-factors-full i h shpᵢ f) (from-transp _ _ shape-path))

M⃗ i O O s f = id
