{-# OPTIONS --without-K --rewriting #-}

{--- Contextual core of a cwf

For an arbitrary internal (wild) cwf we define its contextual core: contexts are
generated from ◆ and _∷_, substitutions from the terminal arrow and _,,_.

We encode this using the unit and Σ types of the host theory as type families of
"codes" Conᶜ and Subᶜ, where Conᶜ is ℕ-indexed (by the length of the
context). The resulting structure is in general *not* a subtype: we generally
don't have a hprop (has-len n Γ) such that
  Σ (n : ℕ) Σ (Γ : Con), has-len n Γ ≃ Σ (n : ℕ), Conᶜ n.

Q's:
∙ What coherence/truncation conditions do we need on the original cwf so that
  the contextual core is again a (wild) cwf?
-}

open import cwfs.CwFs

module cwfs.ContextualCore {ℓₒ ℓₘ} {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C) where

open CwFStructure cwfstr

ext : Σ Con Ty → Con
ext = uncurry _∷_

module Con
  where
  Conᶜ : ℕ → Type ℓₒ
  con : ∀ {n} → Conᶜ n → Con

  Conᶜ O = Lift ⊤
  Conᶜ (1+ n) = Σ (Conᶜ n) (Ty ∘ con)

  con {O} _ = ◆
  con {1+ n} = ext ∘ Σ-fmap-l _ con
    -- this is just (Γᶜ , A) ↦ con Γᶜ ∷ A

open Con public

module Sub
  where
  Subᶜ : ∀ {m n} → Conᶜ m → Conᶜ n → Type ℓₘ
  sub : ∀ {m} {Γᶜ : Conᶜ m} {n} {Δᶜ : Conᶜ n}
        → Subᶜ Γᶜ Δᶜ → Sub (con Γᶜ) (con Δᶜ)

  Subᶜ {n = O} _ _ = Lift ⊤
  Subᶜ {n = 1+ n} Γᶜ (Δᶜ , A) = Σ[ σ ﹕ Subᶜ Γᶜ Δᶜ ] Tm (A [ sub σ ])

  sub {n = 1+ n} (σ , b) = sub σ ,, b
  sub {m = 1+ m} {Γᶜ , A} {n = O} ✶ = (sub {Γᶜ = Γᶜ} ✶) ◦ π A
  sub {m = O} {n = O} ✶ = id

open Sub public

module ◦
  where
  infixr 40 _◦ᶜ_
  _◦ᶜ_ :
    ∀ {k} {Γᶜ : Conᶜ k}
      {m} {Δᶜ : Conᶜ m}
      {n} {Εᶜ : Conᶜ n}
    → Subᶜ Δᶜ Εᶜ → Subᶜ Γᶜ Δᶜ → Subᶜ Γᶜ Εᶜ

  ◦-sub :
    ∀ {k} {Γᶜ : Conᶜ k}
      {m} {Δᶜ : Conᶜ m}
      {n} {Εᶜ : Conᶜ n}
      (g : Subᶜ Δᶜ Εᶜ) (f : Subᶜ Γᶜ Δᶜ)
    → sub g ◦ sub f == sub (g ◦ᶜ f)

  [sub][sub] : -- Auxiliary, also used elsewhere
    ∀ {k} {Γᶜ : Conᶜ k}
      {m} {Δᶜ : Conᶜ m}
      {n} {Εᶜ : Conᶜ n}
      {A : Ty (con Εᶜ)}
      (g : Subᶜ Δᶜ Εᶜ) (f : Subᶜ Γᶜ Δᶜ)
    → A [ sub g ] [ sub f ] == A [ sub (g ◦ᶜ f) ]

  [sub][sub] g f = ![◦] ∙ [= ◦-sub g f ]

  _◦ᶜ_ {n = O} g f = ✶
  _◦ᶜ_ {n = 1+ n} {Εᶜ , A} (g , a) f =
    (g ◦ᶜ f) , coeᵀᵐ ([sub][sub] g f) (a [ sub f ]ₜ)

  ◦-sub {n = O} g f = contr-has-all-paths ⦃ ◆-terminal _ ⦄ _ _
  ◦-sub {n = 1+ n} (g , a) f =
    let rec = ◦-sub g f
    in ,,-◦ ∙ ⟨= rec ,, from-coeᵀᵐˡ (coeᵀᵐ-∙! ![◦] [= rec ]) =⟩

open ◦ public

module substitution
  where
  [sub][sub]ₜ :
    ∀ {k} {Γᶜ : Conᶜ k}
      {m} {Δᶜ : Conᶜ m}
      {n} {Εᶜ : Conᶜ n}
      {A : Ty (con Εᶜ)}
      (a : Tm A) (g : Subᶜ Δᶜ Εᶜ) (f : Subᶜ Γᶜ Δᶜ)
    → a [ sub g ]ₜ [ sub f ]ₜ == a [ sub (g ◦ᶜ f) ]ₜ over⟨ [sub][sub] g f ⟩
  [sub][sub]ₜ a g f = ![◦]ₜ ∙ᵈ [= ◦-sub g f ]ₜ

open substitution public

module associativity
  where
  assᶜ :
    ∀ {k} {Γᶜ : Conᶜ k}
      {l} {Δᶜ : Conᶜ l}
      {m} {Εᶜ : Conᶜ m}
      {n} {Ζᶜ : Conᶜ n}
      (h : Subᶜ Εᶜ Ζᶜ) (g : Subᶜ Δᶜ Εᶜ) (f : Subᶜ Γᶜ Δᶜ)
    → h ◦ᶜ g ◦ᶜ f == (h ◦ᶜ g) ◦ᶜ f

  assᶜ {n = O} _ _ _ = idp
  assᶜ {n = 1+ n} {Ζᶜ , A} (h , a) g f =
    pair= rec (from-transp _ rec eq)
    where
    rec = assᶜ h g f
    eq =
        (transp (λ σ → Tm (A [ sub σ ])) rec
        $ coeᵀᵐ ([sub][sub] h (g ◦ᶜ f))
        $ a [ sub (g ◦ᶜ f) ]ₜ)

      =⟨ app= (transp-∘ Tm ((A [_]) ∘ sub) rec) _ ⟩

        (coeᵀᵐ (ap ((A [_]) ∘ sub) rec)
        $ coeᵀᵐ ([sub][sub] h (g ◦ᶜ f))
        $ a [ sub (g ◦ᶜ f) ]ₜ)

      =⟨ ! (to-transp ([sub][sub]ₜ a g f))
       |in-ctx (coeᵀᵐ (ap ((A [_]) ∘ sub) rec) ∘ coeᵀᵐ ([sub][sub] h _)) ⟩

       (coeᵀᵐ (ap ((A [_]) ∘ sub) rec)
       $ coeᵀᵐ ([sub][sub] h (g ◦ᶜ f))
       $ coeᵀᵐ ([sub][sub] g f)
       $ a [ sub g ]ₜ [ sub f ]ₜ)

      =⟨ coeᵀᵐ-∙! ([sub][sub] h (g ◦ᶜ f)) _ ∙ coeᵀᵐ-∙! ([sub][sub] g f) _ ⟩

        (coeᵀᵐ ([sub][sub] g f ∙ [sub][sub] h (g ◦ᶜ f) ∙ ap ((A [_]) ∘ sub) rec)
        $ a [ sub g ]ₜ [ sub f ]ₜ)

      =⟨ {!!} ⟩ -- pentagon coherence of equalities on internal types!

        (coeᵀᵐ (ap _[ sub f ] ([sub][sub] h g) ∙ [sub][sub] (h ◦ᶜ g) f)
        $ a [ sub g ]ₜ [ sub f ]ₜ)

      =⟨ coeᵀᵐ-∙ (ap _[ sub f ] ([sub][sub] h g)) ([sub][sub] (h ◦ᶜ g) f) ⟩

        (coeᵀᵐ ([sub][sub] (h ◦ᶜ g) f)
        $ coeᵀᵐ (ap _[ sub f ] ([sub][sub] h g))
        $ a [ sub g ]ₜ [ sub f ]ₜ)

      =⟨ to-transp (coeᵀᵐ-[]ₜ-stable ([sub][sub] h g) (a [ sub g ]ₜ) (sub f))
       |in-ctx (coeᵀᵐ ([sub][sub] (h ◦ᶜ g) f)) ⟩

       (coeᵀᵐ ([sub][sub] (h ◦ᶜ g) f)
       $ (coeᵀᵐ ([sub][sub] h g) (a [ sub g ]ₜ)) [ sub f ]ₜ)
      =∎

open associativity public

-- Tyᶜ : ∀ {n} → Conᶜ n → Type (ℓₒ ∪ ℓₘ)
-- Tyᶜ {O} ✶ = Lift {j = ℓₘ} (Ty ◆)
-- Tyᶜ {1+ n} (Γᶜ , A) =
--   ∀ {m} (Δᶜ : Conᶜ m) (σ : Subᶜ Δᶜ Γᶜ) (a : Tm (A [ sub σ ])) → Ty (con Δᶜ)

-- ty-of : ∀ {n} {Γᶜ : Conᶜ n} → Tyᶜ Γᶜ → Ty (con Γᶜ)
-- ty-of {O} (lift A) = A
-- ty-of {1+ n} {Γᶜ , A} Bᶜ = {!!}
