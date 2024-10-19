Substitution in types in a wild cwf should be semipullback (?)

\begin{code}

{-# OPTIONS --without-K --rewriting #-}

module cwfs.Substitution where

open import cwfs.CwFs public

module Substitution-is-semi-pb {ℓₒ} {ℓₘ}
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstruct : CwFStructure C)
  where

  open CwFStructure cwfstruct
  𝒞 = to-wildsemicat C

  open import categories.CommutingSquares 𝒞 public
  open import categories.Semipullbacks 𝒞 public

\end{code}

Refer to the code in `cwfs.CwFs.extension`.

We have the weakening
  σ ∷ₛ A ≡ (σ ◦ π (A[ σ ]) ,, coe!ᵀᵐ [◦] (υ A [ σ ]))
giving the commuting square

           σ ∷ₛ A
    Γ ∷ A[σ] ---> Δ ∷ A
      |             |
      |     ⇗ !βπ   |
      ↓             ↓
      Γ ----------> Δ
             σ

which we call Ty-subst-comm-sq, in the category of contexts.

\begin{code}

  π-cospan : {Γ Δ : Con} (σ : Sub Γ Δ) (A : Ty Δ) → Cospan
  π-cospan {Γ} {Δ} σ A = cospan σ (π A)

  module _ (Γ Δ : Con) (σ : Sub Γ Δ) (A : Ty Δ) where
    Ty-subst-comm-sq : CommSq (π-cospan σ A) (Γ ∷ A [ σ ])
    Ty-subst-comm-sq = square (π (A [ σ ])) (σ ∷ₛ A) (! βπ)

\end{code}

### Lemma
  Ty-subst-comm-sq is a semipullback.
\begin{code}
    Ty-subst-comm-sq-semi-pb-UP : semi-pb-UP _ _ Ty-subst-comm-sq
\end{code}

*Proof.*

Given a commuting square (τ, ρ, γ) with vertex Β as below,

                ρ
      Β ------------------↴
      | ↘ ι      σ ∷ₛ A
      |   Γ ∷ A[σ] ---> Δ ∷ A
    τ |     |             |
      |     |     ⇗ !βπ   |
      |     ↓             ↓
       ⤷    Γ ----------> Δ
                   σ

define the substitution
  ι : Sub Β (Γ ∷ A[σ])
  ι = (τ, υ A [ ρ ]ₜ ◂$ coeᵀᵐ (![◦] ∙ [= ! γ] ∙ [◦]))

Then the left triangle commutes by βπ.

\begin{code}

    Ty-subst-comm-sq-semi-pb-UP Β 𝔖@(square τ ρ γ) =
      ι , fiber-pt , fiber-fst-contr
      where
      ι : Sub Β (Γ ∷ A [ σ ])
      ι = (τ ,, (υ A [ ρ ]ₜ ◂$ coeᵀᵐ (![◦] ∙ [= ! γ ] ∙ [◦])))

      ε₀ : π A ◦ (σ ∷ₛ A) ◦ ι == π A ◦ ρ
      ε₀ = ! ass ∙ (βπ ∗ᵣ ι) ∙ ass ∙ (σ ∗ₗ βπ) ∙ γ

      module scratch where
        σ∷A = σ ∷ₛ A

        basepath : A [ π A ] [ ρ ] == (A [ π A ] [ σ∷A ◦ ι ]) --(A [ π A ] [ ρ ])
        basepath =
          A [ π A ] [ ρ ]    =⟨ ![◦] ⟩
          A [ π A ◦ ρ ]      =⟨ ! [= γ ] ⟩
          A [ σ ◦ τ ]        =⟨ [◦] ⟩
          A [ σ ] [ τ ]      =⟨ ! [= βπ ]  ⟩
          A [ σ ] [ π (A [ σ ]) ◦ ι ]      =⟨ [◦] ⟩
          A [ σ ] [ π (A [ σ ]) ] [ ι ]    =⟨ ![◦] ⁼[ ι ] ⟩
          A [ σ ◦ π (A [ σ ]) ] [ ι ]      =⟨ (! [= βπ ]) ⁼[ ι ] ⟩
          A [ π A ◦ σ∷A ] [ ι ]       =⟨ [◦] ⁼[ ι ] ⟩
          A [ π A ] [ σ∷A ] [ ι ]     =⟨ ![◦] ⟩
          A [ π A ] [ σ∷A ◦ ι ]       --=⟨ ![◦] ⟩
          -- A [ π A ◦ σ∷A ◦ ι ]         =⟨ ! [= ass ] ⟩
          -- A [ (π A ◦ σ∷A) ◦ ι ]       =⟨ [= βπ ∗ᵣ ι ] ⟩
          -- A [ (σ ◦ π (A [ σ ])) ◦ ι ] =⟨ [= ass ] ⟩
          -- A [ σ ◦ π (A [ σ ]) ◦ ι ]   =⟨ [= σ ∗ₗ βπ ] ⟩
          -- A [ σ ◦ τ ]                 =⟨ [= γ ] ⟩
          -- A [ π A ◦ ρ ]   =⟨ [◦] ⟩
          -- A [ π A ] [ ρ ]
          =∎

        scratch =
          υ A [ σ∷A ◦ ι ]ₜ
            =⟨ to-transp' [◦]ₜ ⟩
          υ A [ σ∷A ]ₜ [ ι ]ₜ ↓ᵀᵐ ![◦]
            =⟨ ap (λ □ → □ [ ι ]ₜ ↓ᵀᵐ ![◦]) {!to-transp βυ!} ⟩
          (υ (A [ σ ]) ↓ᵀᵐ ![◦] ∙ ! [= βπ ] ∙ [◦]) [ ι ]ₜ ↓ᵀᵐ ![◦]
          =⟨ {!ap (_↓ᵀᵐ ![◦]) ?!} ⟩
          υ (A [ σ ]) [ ι ]ₜ ↓ᵀᵐ ((![◦] ∙ ! [= βπ ] ∙ [◦]) ⁼[ ι ]) ∙ ![◦]
          =⟨ {!!} ⟩
          υ A [ ρ ]ₜ
            ↓ᵀᵐ basepath
            -- (![◦] ∙ [= ! γ ] ∙ [◦]
            -- ∙ ! [= βπ ] ∙ [◦]
            -- ∙ ((![◦] ∙ ! [= βπ ] ∙ [◦]) ⁼[ ι ]) ∙ ![◦] :>
            --   (A [ π A ] [ ρ ] == A [ π A ] [ σ∷A ◦ ι ]))
          =∎

      -- ε₁' : υ A [ (σ ∷ₛ A) ◦ ι ]ₜ ↓ᵀᵐ 

      ε₁ :
        coe!ᵀᵐ [◦] (υ A [ (σ ∷ₛ A) ◦ ι ]ₜ)
        ==
        coe!ᵀᵐ [◦] (υ A [ ρ ]ₜ)
        over⟨ [= ε₀ ] ⟩
      ε₁ = {!!}

      ε : (σ ∷ₛ A) ◦ ι == ρ
      ε = sub= _ _ ε₀ {!ε₁!}

      fiber-pt : CommSqEq (Ty-subst-comm-sq □ ι) 𝔖
      fiber-pt = βπ , ε , {!!}

      fiber-fst-contr :
        (m : Sub Β ( Γ ∷ A [ σ ]))
        → CommSqEq (Ty-subst-comm-sq □ m) 𝔖
        → m == ι
      fiber-fst-contr = {!!}

\end{code}
