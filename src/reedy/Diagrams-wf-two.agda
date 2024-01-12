{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe
open import hott.WellFounded

module reedy.Diagrams-wf-two {ℓₘᴵ ℓₒ ℓₘ}
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

  {- Nicolai's comment:
     Would it be useful to add  (h ≤ i) to the shape condition?
     We only care about shapes that fulfil this condition.
     We need it in the below record.
     Without this condition, the later type of 𝔸 is wrong,
     as `k ≤ h` doesn't imply `boundary-shape k ≤ₛ s`.

     UPDATE: This is now added to the shape condition.
  -}


{-
  The data that we construct by shape induction consists of
  𝔻, Mᵒ, M⃗, M⃗∘, γ (working name) 
  TODO: decide what exactly these are!
  E.g., for 𝔻, we might want to ignore everything apart from `h`.
  However, there's an off-by-1, as M (i,h,t) needs 𝔻 (1+ h).
  So, do we need to re-interpret h as h-1 here? Or what do we do?

  Ugly solution would be to skip 0, and say that `𝔻 s` should have length `1+ (ℎ s)`.

-}
record ind-data (s : Shape) : Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) where
  i = 𝑖 s
  h = ℎ s
  t = 𝑡 s

  h≤i : h ≤ i
  h≤i = fst (is-s s)

  t≤max = snd (is-s s)
  
  
  field
    𝔻  : Con -- interpretation: ignore everything but `h` in `s`
    Mᵒ  : (s' : Shape) → (s' ≤ₛ s) → Tel 𝔻

  -- convenience definitions
  M : ∀ (s' : Shape) → (s' ≤ₛ s) → Con
  M s' q = close (Mᵒ s' q)

  Mᵒᵗᵒᵗ : (i : ℕ) → (boundary-shape i ≤ₛ s) → Tel 𝔻
  Mᵒᵗᵒᵗ i q = Mᵒ (boundary-shape i) q


  {- todo: give names to the shapes in the Cosieves file.
  Mᵒᶠᵘˡˡ : (i h : ℕ) → Tel (𝔻 (1+ h))
  Mᵒᶠᵘˡˡ i h = Mᵒ i h full shp
    where
    full = hom-size i h
    shp = full-shape i h
  -}

  -- Mᵒᵗᵒᵗ : (i : ℕ) → (i ≤ 1+ h) → Tel 𝔻  -- i < or i ≤ 1+ h?
  -- Mᵒᵗᵒᵗ = {!!}

  -- (Ideally, give a name to the prove of `boundary-shape i ≤ₛ s`
  --  since we need it multiple times.)

  𝔸 : (k : ℕ) → (k ≤ h) → Ty 𝔻
  𝔸 k k≤h = Πₜₑₗ (Mᵒᵗᵒᵗ k (boundary-smaller {k} {s} k≤h)) U

  A : (k : ℕ) → (k≤h : k ≤ h) → Ty (𝔻 ∷ 𝔸 k k≤h ++ₜₑₗ  Mᵒᵗᵒᵗ k (boundary-smaller {k} {s} k≤h) [ π (𝔸 k k≤h) ]ₜₑₗ  )
  A k k≤h = generic[ Mᵒᵗᵒᵗ k (boundary-smaller {k} {s} k≤h) ]type

  field
    M⃗  : ∀ {s' : Shape} → (s'≤s : s' ≤ₛ s)
            → {k : ℕ} → (f : hom (𝑖 s') k)
            → Sub (close $ Mᵒ s' s'≤s)
                  (close $ Mᵒ (s' · f)
                              (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' f) s'≤s)))

  M[·comp] : ∀ (s' : Shape) → (s'≤s : s' ≤ₛ s)
             → {k : ℕ} → (f : hom (𝑖 s') k)
             → {l : ℕ} → (g : hom k l)
             → Mᵒ (s' · (g ◦ f)) (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' (g ◦ f)) s'≤s))
               ==
               Mᵒ ((s' · f) · g) (inr (<ₛ-≤ₛ-<ₛ (·<ₛ (s' · f) g) (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' f) s'≤s))))
  M[·comp] s' s'≤s {k} f {l} g
           = {! (apd Mᵒ (∙comp s' f g)) !}

  -- We could transport along this equality. However, it's nicer to
  -- use the usual `id2iso`, here called `idd`, and compose with that:

  field
    M⃗∘ : ∀ {s' : Shape} → (s'≤s : s' ≤ₛ s)
             → {k : ℕ} → (f : hom (𝑖 s') k)
             → {l : ℕ} → (g : hom k l)
             → (M⃗ {s' = s' · f} (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' f) s'≤s)) g)
                   ◦ˢᵘᵇ (M⃗ {s' = s'} s'≤s f)
               ==
               idd (ap close (M[·comp] s' s'≤s f g))
                   ◦ˢᵘᵇ (M⃗ {s' = s'} s'≤s (g ◦ f))

    -- γ : {!!}

Main-construction : (s : Shape) → ind-data s
Main-construction =
  shape-ind ind-data

    -- case (i,O,O)
    (λ i ih →
      record {
        𝔻 = {!!}
        ;
        Mᵒ = λ _ _ → •
        ;
        M⃗ = {!!}
        ;
        M⃗∘ = {!!}
      })

    -- case (i,h+1,O)
    (λ i h 1+h≤i ih →
      record {
        𝔻 = {!!}
        ;
        Mᵒ = {!!}
        ;
        M⃗ = {!!}
        ;
        M⃗∘ = {!!}
      })

    -- case (i,h,t+1)
    (λ i h t is-s ih →
      record {
        𝔻 = {!!}
        ;
        Mᵒ = {!!}
        ;
        M⃗ = {!!}
        ;
        M⃗∘ = {!!}
      })




