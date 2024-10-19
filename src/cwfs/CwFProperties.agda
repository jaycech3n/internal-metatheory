{-# OPTIONS --without-K --rewriting #-}

open import cwfs.CwFs

module cwfs.CwFProperties {ℓₒ ℓₘ}
  {C : WildCategory ℓₒ ℓₘ}
  (cwfStr : CwFStructure C)
  where

open CwFStructure cwfStr public

idd-ap-∷ :
  ∀ {Γ} {A A' : Ty Γ} (p : A == A')
  → idd (ap (Γ ∷_) p) == (π A ,, (υ A ↓ᵀᵐ (p ⁼[ π A ])))
idd-ap-∷ idp = ! η,,

module _ {Γ Δ : Con} {A : Ty Δ} where
  sub=' : (f g : Sub Γ (Δ ∷ A))
    → (p : π A ◦ f == π A ◦ g)
    → υ A [ f ]ₜ ↓ᵀᵐ ![◦] ∙ [= p ] == υ A [ g ]ₜ ↓ᵀᵐ ![◦]
    → f == g
  sub=' f g p q =
    ! (,,-η f)
    ∙ ap (uncurry _,,_) (pair= p (from-transp _ p q'))
    ∙ ,,-η g
    where
    q' : transp (Tm ∘ (A [_])) p (υ A [ f ]ₜ ↓ᵀᵐ ![◦])
         == υ A [ g ]ₜ  ↓ᵀᵐ ![◦]
    q' = transp (Tm ∘ (A [_])) p (υ A [ f ]ₜ ↓ᵀᵐ ![◦])
         =⟨ transp[=] p ⟩
         (υ A [ f ]ₜ ↓ᵀᵐ ![◦]) ↓ᵀᵐ [= p ]
         =⟨ ! $ transp-∙ ![◦] [= p ] _ ⟩
         _
         =⟨ q ⟩
         υ A [ g ]ₜ  ↓ᵀᵐ ![◦]
         =∎

  lemma? : (f g : Sub Γ (Δ ∷ A))
    → (p : π A ◦ f == π A ◦ g)
    → (q : υ A [ f ]ₜ ↓ᵀᵐ ![◦] ∙ [= p ] == υ A [ g ]ₜ ↓ᵀᵐ ![◦])
    → π A ∗ₗ sub=' f g p q == p
  lemma? f g p q =
    π A ∗ₗ
      (! (,,-η f)
      ∙ (ap (uncurry _,,_) (pair= p _)
      ∙ ,,-η g))

    =⟨ ∗ₗ-∙ _ (! $ ,,-η f) (ap (uncurry _,,_) (pair= p _) ∙ ,,-η g)
      ∙ ap ((π A ∗ₗ ! (,,-η f)) ∙_) (∗ₗ-∙ _ _ (,,-η g)) ⟩

      (π A ∗ₗ ! (,,-η f))
      ∙ (π A ∗ₗ ap (uncurry _,,_) (pair= p _))
      ∙ (π A ∗ₗ (,,-η g))

    =⟨ idp ⟩

      (π A ∗ₗ ! (,,-η f))
      ∙ ap (π A ◦_) (ap (uncurry _,,_) (pair= p _))
      ∙ (π A ∗ₗ (,,-η g))

    =⟨ ! (ap-∘ (π A ◦_) (uncurry _,,_) (pair= p _))
     |in-ctx (λ □ → (π A ∗ₗ ! (,,-η f)) ∙ □ ∙ (π A ∗ₗ (,,-η g))) ⟩

      (π A ∗ₗ ! (,,-η f))
      ∙ (ap ((π A ◦_) ∘ (uncurry _,,_)) (pair= p _))
      ∙ (π A ∗ₗ (,,-η g))
    =⟨ idp ⟩

      (π A ∗ₗ ! (,,-η f))
      ∙ (ap (λ{ (σ , a ) → π A ◦ (σ ,, a) }) (pair= p _))
      ∙ (π A ∗ₗ (,,-η g))

    =⟨ {!!} ⟩

      (π A ∗ₗ ! (,,-η f))
      ∙ (ap (λ{ (σ , a ) → π A ◦ (σ ,, a) }) (pair= p _))
      ∙ (π A ∗ₗ (,,-η g))

    =⟨ {!!} ⟩
    p
    =∎
