{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

{--- IMPORTANT! This version switches off termination checking temporarily. ---}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import hott.WellFounded

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


Shape = Σ[ (i , h , t) ː ℕ × ℕ × ℕ ] shape i h t


_<ₛ_ : Shape → Shape → Type₀
((i₁ , h₁ , t₁) , shape₁) <ₛ ((i₂ , h₂ , t₂) , shape₂) = {!(i₁ < i₂) OR ... (lexicographic order)!}

iswf<ₛ : is-wf _<ₛ_
iswf<ₛ = {!!}

record ind-data (s : Shape) : Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) where
  field
    SCT : Con
    Mᵒ  : ∀ {s' : Shape} → ((s' <ₛ s) ⊔ (s' == s)) → Tel SCT
    M⃗  : ∀ {s' : Shape} → ((s' <ₛ s) ⊔ (s' == s))
            → {k : ℕ} → (f : hom (fst (fst s')) k) → Sub (close $ Mᵒ (inr idp)) (close $ Mᵒ {s' = {!s' · f!}} {!inl $ lemma : s' · f <ₛ s!})
    α   : ∀ {s' : Shape} → (p : ((s' <ₛ s) ⊔ (s' == s)))
            → {k : ℕ} → (f : hom (fst (fst s')) k)
            → {l : ℕ} → (g : hom k l)
            → (M⃗ {s' = {!s' ◦ f!}} {!lemma!} g) ◦ˢᵘᵇ (M⃗ {s' = s'} p f) == (M⃗ {s' = s'} p (g ◦ f))
    γ   : {!!}



{-
𝔻ₜ : ℕ → Con
Mᵒₜ = (i h t : ℕ) → (𝔻 : 𝔻ₜ) → shape i h t → Tel (𝔻 (1+ h))

-- Convenience definitions ====

-- Mₜ = (i h t : ℕ) → shape i h t → Con
-- M i h t s = close (Mᵒ i h t s)

Mᵒₜₒₜ : (i : ℕ) → Tel (𝔻 i)
Mᵒₜₒₜ O = •
Mᵒₜₒₜ (1+ i) = Mᵒ (1+ i) i (hom-size (1+ i) i) (total-shape-1+ i)

𝔸 : (i : ℕ) → Ty (𝔻 i)
𝔸 i = Πₜₑₗ (Mᵒₜₒₜ i) U

A : (i : ℕ) → Ty (𝔻 i ∷ 𝔸 i ++ₜₑₗ Mᵒₜₒₜ i [ π (𝔸 i) ]ₜₑₗ)
A i = generic[ Mᵒₜₒₜ i ]type

-- End convenience definitions ====

test : _
test = {!Σ[ x ∶ ℕ ] ?!}


𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f
        sh = count-factors-gives-shape i h t s f
    in Sub (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ i h t s) (𝔻 h ∷ 𝔸 h ++ₜₑₗ Mᵒ j h cf sh)



M⃗ = {!!}

{-
{-# TERMINATING #-}
Mᵒ i h (1+ t) s =
  Mᵒ i h t shp ‣ A h [ {!!} ◦ˢᵘᵇ M⃗ i h t shp (#[ t ] i h u) ]
  where
  shp = prev-shape s
  u : t < hom-size i h
  u = S≤-< s
Mᵒ i (1+ h) O s = Mᵒ i h full shp [ π (𝔸 (1+ h)) ]ₜₑₗ
  where
  full = hom-size i h
  shp = full-shape i h
Mᵒ i O O s = •

M⃗ i h (1+ t) s f = {!!}
M⃗ i (1+ h) O s f = {!M⃗ i h full shp !}
  where
  full = hom-size i h
  shp = full-shape i h
M⃗ i O O s f = id
-}
-}
