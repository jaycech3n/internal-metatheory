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

M= : ∀ i h {t} {s} {t'} {s'} → t == t' → M i h t s == M i h t' s'
M= i h {t} {s} {.t} {s'} idp = ap (M i h t) shape-path

-- End convenience definitions ====

𝔻 O = ◆
𝔻 (1+ i) = 𝔻 i ∷ 𝔸 i

M⃗ :
  ∀ i h t s {j} (f : hom i j)
  → let cf = count-factors i h t s f
        sh = count-factors-shape i h t s f
    in Sub (M i h t s) (M j h cf sh)


-- Also use this equation
M=₁ :
  ∀ i h t (s : shape i h (1+ t))
  → let prev = prev-shape s
        u = S≤-< s
        [t] = #[ t ] i h u
        cf = count-factors i h t prev [t]
        sh = count-factors-shape i h t prev [t]
    in M h h cf sh == close (Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)


M⃗◦ :
  ∀ i h t s {j} (f : hom i j) {k} (g : hom j k)
  → let cf = count-factors i h t s f
        sh = count-factors-shape i h t s f -- or abstract over this too?
        p  = count-factors-comp i h t s f g -- and this too?
    in M⃗ j h cf sh g ◦ˢᵘᵇ M⃗ i h t s f == idd (M= k h p) ◦ˢᵘᵇ M⃗ i h t s (g ◦ f)


{-# TERMINATING #-}
Mᵒ i h (1+ t) s =
  Mᵒ i h t shp ‣ A h [ idd eq ◦ˢᵘᵇ M⃗ i h t shp (#[ t ] i h u) ]
  where
  shp = prev-shape s
  u : t < hom-size i h
  u = S≤-< s

  c = count-factors i h t shp (#[ t ] i h u)
  cs = count-factors-shape i h t shp (#[ t ] i h u)

  eq : M h h c cs == (𝔻 (1+ h) ++ₜₑₗ Mᵒᵗᵒᵗ h [ π (𝔸 h) ]ₜₑₗ)
  eq = M=₁ i h t s

Mᵒ i (1+ h) O s = Mᵒᶠᵘˡˡ i h [ π (𝔸 (1+ h)) ]ₜₑₗ
Mᵒ i O O s = •

M=₁ i O t s =
  M O O cf sh =⟨ M= O O {s' = O≤ _} p ⟩
  M O O O (O≤ (hom-size O O)) =⟨ idp ⟩
  close (Mᵒᵗᵒᵗ O [ π (𝔸 O) ]ₜₑₗ) =∎
  where
  prev = prev-shape s
  u = S≤-< s
  [t] = #[ t ] i O u
  cf = count-factors i O t prev [t]
  sh = count-factors-shape i O t prev [t]

  p : cf == O
  p = count-factors-top-level i O t prev [t]

M=₁ i (1+ h) t s =
  M (1+ h) (1+ h) cf sh =⟨ M= (1+ h) (1+ h) {s' = O≤ _} p ⟩
  M (1+ h) (1+ h) O (O≤ _) =⟨ idp ⟩
  close (Mᵒᵗᵒᵗ (1+ h) [ π (𝔸 (1+ h)) ]ₜₑₗ) =∎
  where
  prev = prev-shape s
  u = S≤-< s
  [t] = #[ t ] i (1+ h) u
  cf = count-factors i (1+ h) t prev [t]
  sh = count-factors-shape i (1+ h) t prev [t]

  p : cf == O
  p = count-factors-top-level i (1+ h) t prev [t]


M⃗ i h (1+ O) s {j} f =
  show Sub (M i h (1+ O) s) (M j h c cs) by
  depcase
    (λ d →
      Sub (M i h (1+ O) s)
          (M j h (count-factors[ i , h ,1+ O ] u f d)
                 (count-factors-shape-aux i h O u f d)))
    (f ∣? #[ O ] i h u)
    (λ (g , e) → {!!})
    λ no → M⃗ i h O prev f ◦ˢᵘᵇ π (A h [ _ ])
  where
  c = count-factors i h (1+ O) s f
  cs = count-factors-shape i h (1+ O) s f
  u = S≤-< s
  prev = prev-shape s

M⃗ i h (2+ t) s {j} f = show Sub (M i h (2+ t) s) (M j h c cs) by
  depcase
    (λ d →
      Sub (M i h (2+ t) s)
          (M j h (count-factors[ i , h ,1+ 1+ t ] u f d)
                 (count-factors-shape-aux i h (1+ t) u f d)))
    (f ∣? #[ 1+ t ] i h u)
    (λ (g , e) → {!!})
    λ no → {!M⃗ i h (1+ t) ? f ◦ˢᵘᵇ π (A h [ _ ])
      -- Definitional mismatch blocks the above from going through:
      -- need that S≤-< (S≤-≤ s) ≡ S<-< (S≤-< s).!}
  where
  c = count-factors i h (2+ t) s f
  cs = count-factors-shape i h (2+ t) s f
  u = S≤-< s
  prev = prev-shape s

{- new attempts
--  with f ∣ #[ t ] i h (S≤-< s)
--     -- | count-factors i h (1+ t) s f in eq
--     -- | count-factors-shape i h (1+ t) s f
--     | Mᵒ j h (count-factors i h (1+ t) s f)
--         (count-factors-shape i h (1+ t) s f)
--     -- | inspect (uncurry $ Mᵒ j h)
--     --           ( count-factors i h (1+ t) s f
--     --           , count-factors-shape i h (1+ t) s f )
-- ... | inl x | Mᵒjh = {!!}
-- ... | inr x | Mᵒjh = {!!}
-}

{- old def
 with f ∣ #[ t ] i h (S≤-< s)
    | inspect (count-factors i h (1+ t) s) f
    | count-factors i h (1+ t) s f               -- c
    | inspect (count-factors i h (1+ t) s) f
    | count-factors-shape i h (1+ t) s f   -- cs
    | Mᵒ j h (count-factors i h (1+ t) s f)
        (count-factors-shape i h (1+ t) s f)
    | inspect (uncurry $ Mᵒ j h)
        (count-factors i h (1+ t) s f
        , count-factors-shape i h (1+ t) s f)

... | inl (g , e)
    | have p -- : count-factors i h (1+ t) s f ==
             --   1+ (count-factors i h t (prev-shape s) f)
    | c @ .(count-factors i h (1+ t) s f) | have idp
    | cs
    | .(Mᵒ j h (count-factors i h (1+ t) s f) cs) | have idp
      -- Would we be able to pattern match on p if we paired up c and its
      -- inspected equality? More principled: worth manually writing auxiliary
      -- defs to do a proper hand-tailored with-abstraction.
    =
    (idd eq ◦ˢᵘᵇ
      (idd {!!} ◦ˢᵘᵇ M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ]) ,, {!!})
    ) :> (Sub (M i h t prev ∷ A h [ idd (M=₁ i h t s) ◦ˢᵘᵇ M⃗iht[t] ]) (M j h c cs))
    where
    prev = prev-shape s
    cf = count-factors i h t prev f

    sh : shape j h (1+ cf)
    sh = transp (shape j h) p cs

    eq : M j h (1+ cf) sh == M j h c cs
    eq = M= j h (! p)

    -- debugging
    u = S≤-< s
    M⃗iht[t] = M⃗ i h t prev (#[ t ] i h u)
    ----

    M⃗ihtf = M⃗ i h t prev f

... | inr no
    | have p -- : count-factors i h (1+ t) s f ==
             --   count-factors i h t (prev-shape s) f
    | c @ .(count-factors i h (1+ t) s f) | have idp
    | cs
    | .(Mᵒ j h (count-factors i h (1+ t) s f) cs) | have idp
    =
    idd eq ◦ˢᵘᵇ M⃗ i h t prev f ◦ˢᵘᵇ π (A h [ _ ])
      -- Note (also record this on paper): on paper, don't have this coercion by
      -- (idd _), but in TT we need this because we don't have that
      -- count-factors (i, h, t+1) f reduces to count-factors (i, h, t) f
      -- definitionally. But maybe it can be made so, with more effort?
    where
    prev = prev-shape s
    cf = count-factors i h t prev f
    sh = count-factors-shape i h t prev f

    eq : M j h cf sh == M j h c cs
    eq = M= j h (! p)
-}

M⃗ i (1+ h) O s {j} f =
  wkn-sub (Mᵒᶠᵘˡˡ i h) (Mᵒᶠᵘˡˡ j h)
    (idd eq ◦ˢᵘᵇ M⃗ i h fullᵢ shpᵢ f)
    {!commutation lemma; another component of the definition!}
    (𝔸 (1+ h))
  where
  fullᵢ = hom-size i h
  shpᵢ = full-shape i h

  cf = count-factors i h fullᵢ shpᵢ f
  sh = count-factors-shape i h fullᵢ shpᵢ f

  fullⱼ = hom-size j h
  shpⱼ = full-shape j h

  eq : M j h cf sh == M j h fullⱼ shpⱼ
  eq = M= j h (count-factors-full i h shpᵢ f)

M⃗ i O O s f = id


M⃗◦ = {!!}
