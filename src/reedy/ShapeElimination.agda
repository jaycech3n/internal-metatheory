{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.SimpleSemicategories

module reedy.ShapeElimination {ℓₘ} (I : SimpleSemicategory ℓₘ) where

open import reedy.Cosieves I public

record ShapeElimData {ℓ}
  (C : (i h t : ℕ) → shape i h t → Type ℓ)
  (i h t : ℕ) (s : shape i h t)
  : Type ℓ
  where
  constructor shape-cases
  field
    c0 : (i : ℕ) (s : shape i 0 0)
       → -------------------------
         C i 0 0 s

    ch : (i h : ℕ)
         (s : shape i (1+ h) 0)
         (f : ∀ j h' t' s' → j < i → C j h' t' s')
         (g : ∀ h' t' s' → h' < h → C i h' t' s')
      →  -----------------------------------------
         C i (1+ h) 0 s

    ct : (i h t : ℕ)
         (s : shape i h (1+ t))
         (f : ∀ j h' t' s' → j < i → C j h' t' s')
         (g : ∀ t' s' → t' < t → C i h t' s')
      →  -----------------------------------------
         C i h (1+ t) s

module _ {ℓ} (C : (i h t : ℕ) → shape i h t → Type ℓ) where
  shape-elim-aux-h : (i₀ h₀ t₀ : ℕ) → ShapeElimData C
    → (i h t : ℕ) (s : shape i h t)
    → i ≤ i₀ → h < h₀
    → C i h t s
  shape-elim-aux-t : (i₀ h₀ t₀ : ℕ) → ShapeElimData C
    → (t : ℕ) (s : shape i₀ h₀ t)
    → t ≤ t₀
    → C i₀ h₀ t s

  shape-elim-aux-h O (1+ O) t₀ (shape-cases c0 ch ct) .O .O O s (inl idp) ltS = c0 0 s
  shape-elim-aux-h O (1+ O) t₀ (shape-cases c0 ch ct) .O .O (1+ t) s (inl idp) ltS = {!!}
  shape-elim-aux-h O (2+ h₀) t₀ (shape-cases c0 ch ct) .O h t s (inl idp) uₕ = {!!}
  shape-elim-aux-h (1+ i₀) h₀ t₀ (shape-cases c0 ch ct) i h t s uᵢ uₕ = {!!}

  shape-elim-aux-t i₀ h₀ t₀ (shape-cases c0 ch ct) t s uₜ = {!!}


module old where
  shape-elim-aux :
    ∀ {ℓ} (C : (i h t : ℕ) → shape i h t → Type ℓ)
    → (i₀ h₀ t₀ : ℕ)
    →
      (  (i : ℕ) (s : shape i 0 0)
      →  -------------------------
         C i 0 0 s )
    →
      (  (i h : ℕ)
         (s : shape i (1+ h) 0)
         (f : ∀ j h' t' s' → j < i → C j h' t' s')
         (g : ∀ h' t' s' → h' < h → C i h' t' s')
      →  -----------------------------------------
         C i (1+ h) 0 s )
    →
      (  (i h t : ℕ)
         (s : shape i h (1+ t))
         (f : ∀ j h' t' s' → j < i → C j h' t' s')
         (g : ∀ t' s' → t' < t → C i h t' s')
      →  -----------------------------------------
         C i h (1+ t) s )

    → (i h t : ℕ) (s : shape i h t)
    → i ≤ i₀ → h ≤ h₀ → t ≤ t₀ -- This is wrong: need to separately consider
                               -- (i ≤ iₒ and h ≤ h₀) and (i₀, h₀, t ≤ t₀).
    → C i h t s

  shape-elim-aux C i₀ h₀ (1+ t₀) c0 ch ct i h t s uᵢ uₕ uₜ = {!!}
  shape-elim-aux C i₀ (1+ h₀) O c0 ch ct
    .i₀ .(1+ h₀) .O s (inl idp) (inl idp) (inl idp)
    = ch i₀ h₀ s f {!!}
    where
    f : (j h' t' : ℕ) (s' : shape j h' t') → j < i₀ → C j h' t' s'
    f j h' t' s' ltS = {!shape-elim-aux C j !}
    f j h' t' s' (ltSR u) = {!!}
  shape-elim-aux C i₀ (1+ h₀) O c0 ch ct
    i .(1+ h₀) .O s (inr uᵢ) (inl idp) (inl idp)
    = {!!}
    -- = ch i h₀ s f g
    -- where
    -- f : (j h' t' : ℕ) (s' : shape j h' t') → j < i → C j h' t' s'
    -- f j h' t' s' u = {!!}

    -- g : (h' t' : ℕ) (s' : shape i h' t') → h' < h₀ → C i h' t' s'
    -- g h' t' s' u = {!!}
  shape-elim-aux C i₀ (1+ h₀) O c0 ch ct i h t s uᵢ (inr uₕ) uₜ
    = shape-elim-aux C i₀ h₀ O c0 ch ct i h t s uᵢ (<S-≤ uₕ) uₜ
  shape-elim-aux C i₀ O O c0 ch ct i h t s uᵢ (inl idp) (inl idp) = c0 i s


module old-old where
  shape-elim-old :
    ∀ {ℓ} (C : (i h t : ℕ) → shape i h t → Type ℓ)
    →
      ( (i : ℕ)  (s : shape i 0 0)
      → --------------------------
               C i 0 0 s )
    →
      (       (i h : ℕ)      (s : shape i (1+ h) 0)
        (f : ∀ j h' t' s' → j ≤ i → h' ≤ h → C j h' t' s')
      → --------------------------------------------------
                         C i (1+ h) 0 s )
    →
      (          (i h t : ℕ)        (s : shape i h (1+ t))
        (f : ∀ j h' t' s' → j ≤ i → h' ≤ h → t' < t → C j h' t' s')
      → -----------------------------------------------------------
                            C i h (1+ t) s )

    → (i h t : ℕ) (s : shape i h t) → C i h t s

  shape-elim-old C c0 ch ct i h (1+ t) s = {!!}
  shape-elim-old C c0 ch ct O O O s = c0 0 s
  shape-elim-old C c0 ch ct O (1+ h) O s = ch O h s f
    where
    f : (j h' t' : ℕ) (s' : shape j h' t') → j ≤ O → h' ≤ h → C j h' t' s'
    f .O O t' s' (inl idp) v = shape-elim-old C c0 ch ct O O t' s'
    f .O (1+ h') t' s' (inl idp) (inl idp) = shape-elim-old C c0 ch ct O h t' s'
    f .O (1+ h') t' s' (inl idp) (inr v) = {!v!}
  shape-elim-old C c0 ch ct (1+ i) h O s = {!!}
