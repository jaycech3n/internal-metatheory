{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

{--- IMPORTANT! This version switches off termination checking temporarily. ---}

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



record ind-data (s : Shape) : Type (ℓₘᴵ ∪ ℓₒ ∪ ℓₘ) where
  i = 𝑖 s
  h = ℎ s
  t = 𝑡 s
  
  field
    𝔻  : Con
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

  𝔸 : (i : ℕ) → (i ≤ h) → Ty 𝔻
  𝔸 i q = Πₜₑₗ (Mᵒᵗᵒᵗ i {!!}) U
  {- Nicolai's comment:
     Would it be useful to add  (h ≤ i) to the shape condition?
     We only care about shapes that fulfil this condition.
     Without this condition, the above type of 𝔸 is wrong,
     as `i ≤ h` doesn't imply `boundary-shape i ≤ₛ s`.
     (Ideally, give a name to the prove of `boundary-shape i ≤ₛ s`
     since we need it multiple times.)
  -}

  A : (i : ℕ) → (q : i ≤ h) → Ty (𝔻 ∷ 𝔸 i q ++ₜₑₗ  Mᵒᵗᵒᵗ i {!!} [ π (𝔸 i {!!}) ]ₜₑₗ  )
  A i q = generic[ Mᵒᵗᵒᵗ i {!!} ]type
  {-

  M= : ∀ i h {t} {s} {t'} {s'} → t == t' → M i h t s == M i h t' s'
  M= i h {t} {s} {.t} {s'} idp = ap (M i h t) shape-path

  M=' :
    ∀ i h t t' {s} {s'}
    → t == t'
    → M i h t s == M i h t' s'
  M=' i h t t' {s} {s'} p = M= i h {s = s} {s' = s'} p
  -}
  {-
  
  field
    M⃗ : ∀ i h t s {j} (f : hom i j)
         → let cf = count-factors i h t s f
               sh = count-factors-shape i h t s f
           in Sub (M (i h t s) (M j h cf sh)

  field
    M⃗  : ∀ {s' : Shape} → (p : s' ≤ₛ s)
            → {k : ℕ} → (f : hom (𝑖 s') k)
            → Sub (close $ Mᵒ p)
                  (close $ Mᵒ {s' = s' · f}
                              (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' f) p)))

  id-iso : ∀ (s' : Shape) → (p : s' ≤ₛ s)
             → {k : ℕ} → (f : hom (𝑖 s') k)
             → {l : ℕ} → (g : hom k l)
             → Sub (close $ Mᵒ (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' (g ◦ f)) p)))
                   (close $ Mᵒ (inr (<ₛ-≤ₛ-<ₛ (·<ₛ (s' · f) g) (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' f) p)))))
  id-iso = {!transp {A = Σ[!}

-- !! or use Josh's strategy (maybe better?); cf Diagrams.agda

  field
    M⃗∘ : ∀ {s' : Shape} → (p : s' ≤ₛ s)
             → {k : ℕ} → (f : hom (𝑖 s') k)
             → {l : ℕ} → (g : hom k l)
             → (M⃗ {s' = s' · f} (inr (<ₛ-≤ₛ-<ₛ (·<ₛ s' f) p)) g)
                   ◦ˢᵘᵇ (M⃗ {s' = s'} p f)
               ==
               (id-iso s' p f g) ◦ˢᵘᵇ (M⃗ {s' = s'} p (g ◦ f))

    -- γ   : {!!}
  -}



{-


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

M=' :
  ∀ i h t t' {s} {s'}
  → t == t'
  → M i h t s == M i h t' s'
M=' i h t t' {s} {s'} p = M= i h {s = s} {s' = s'} p

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
  Mᵒ i h t prev ‣ A h [ idd eq ◦ˢᵘᵇ M⃗ i h t prev (#[ t ] i h u) ]
  where
  prev = prev-shape s
  u : t < hom-size i h
  u = S≤-< s

  c = count-factors i h t prev (#[ t ] i h u)
  cs = count-factors-shape i h t prev (#[ t ] i h u)

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
  depcase P
    (f ∣? #[ O ] i h u)
    yes.sub
    no.sub
  :>
  Sub (M i h 1 s)
      (M j h (count-factors i h 1 s f)
        (count-factors-shape i h 1 s f))
  where
  u : O < hom-size i h
  u = S≤-< s

  f∣[O] : Type _
  f∣[O] = f ∣ #[ O ] i h u

  P : (d : Dec f∣[O]) → Type _
  P d = Sub (M i h 1 s)
            (M j h (count-factors[ i , h ,1+ O ] u f d)
              (count-factors-shape-aux i h O u f d))

  module yes (w : f∣[O]) where
    prev = prev-shape s

    p : count-factors i h O prev f == O
    p = idp

    sub : Sub (M i h 1 s) (M j h O _ ∷ A h [ _ ])
    sub =
      idd (M= j h p) ◦ˢᵘᵇ M⃗ i h O prev f ◦ˢᵘᵇ π (A h [ _ ])
      ,, {!!}

  module no (w : ¬ f∣[O]) where
    prev = prev-shape s

    sub : Sub (M i h 1 s) (M j h O _)
    sub = M⃗ i h O prev f ◦ˢᵘᵇ π (A h [ _ ])

  prev = prev-shape s

M⃗ i h (2+ t) s {j} f =
  depcase P
    (f ∣? #[ 1+ t ] i h u)
    yes.sub
    no.sub
  :>
  Sub (M i h (2+ t) s)
      (M j h (count-factors i h (2+ t) s f)
        (count-factors-shape i h (2+ t) s f))
  where
  u : 1+ t < hom-size i h
  u = S≤-< s

  f∣[t+1] : Type _
  f∣[t+1] = f ∣ #[ 1+ t ] i h u

  P : (d : Dec f∣[t+1]) → Type _
  P d = Sub (M i h (2+ t) s)
            (M j h (count-factors[ i , h ,1+ 1+ t ] u f d)
              (count-factors-shape-aux i h (1+ t) u f d))

  module yes (w : f∣[t+1]) where
    prev = prev-shape s

    v : t < hom-size i h
    v = S<-< u

    p : count-factors i h (1+ t) prev f ==
        count-factors[ i , h ,1+ t ] v f (f ∣? #[ t ] i h v)
    p = idp

    sub : Sub (M i h (2+ t) s)
              (M j h (count-factors i h (1+ t) prev f) _ ∷ A h [ _ ])
    sub =
      idd (M= j h p) ◦ˢᵘᵇ M⃗ i h (1+ t) prev f ◦ˢᵘᵇ π (A h [ _ ])
      ,, {!!}

  module no (w : ¬ f∣[t+1]) where
    prev = prev-shape s

    sub : Sub (M i h (2+ t) s)
              (M j h (count-factors i h (1+ t) prev f) _)
    sub = M⃗ i h (1+ t) prev f ◦ˢᵘᵇ π (A h [ _ ])

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


-}
