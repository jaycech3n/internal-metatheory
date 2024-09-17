{-# OPTIONS --without-K --rewriting #-}

module cwfs.CwFs where

open import cwfs.Base public

-- Precoherent CwFs
record CwFStructure {ℓₒ ℓₘ} (C : WildCategory ℓₒ ℓₘ) : Type (lsuc (ℓₒ ∪ ℓₘ))
  where

  field compstr : ComprehensionStructure C
  open ComprehensionStructure compstr hiding (tytmstr) public

  private
    module notation where
      infixl 40 ap↓-Tm
      ap↓-Tm : {Γ Δ : Con} {f : Ty Γ → Ty Δ}
          (g : {A : Ty Γ} → Tm A → (Tm ∘ f) A)
          {A A' : Ty Γ} {p : A == A'}
          {a : Tm A} {a' : Tm A'}
        → a == a' [ Tm ↓ p ]
        → g a == g a' [ Tm ↓ ap f p ]
      ap↓-Tm g q = ap↓² {A = Con} {B = Ty} {C = Tm} g q
      syntax ap↓-Tm g q = q |in-ctx↓ᵀᵐ g

      Tm[_] : ∀ Γ → Ty Γ → Type ℓₘ
      Tm[ _ ] A = Tm A

      infix 999 _ʷ _ʷₜ
      _ʷ : {Γ : Con} {A : Ty Γ} → Ty Γ → Ty (Γ ∷ A)
      _ʷ {A = A} B = B [ π A ]

      _ʷₜ : {Γ : Con} {A B : Ty Γ} → Tm B → Tm (B [ π A ])
      _ʷₜ {A = A} b = b [ π A ]ₜ

      instance
        witness-∷ : {Γ : Con} {A : Ty Γ} → Γ ∷ A == Γ ∷ A
        witness-∷ = idp

      var : {Γ : Con} {A : Ty Γ} (Δ : Con) → ⦃ Δ == Γ ∷ A ⦄ → Tm[ Γ ∷ A ] (A ʷ)
      var {Γ} {A} .(Γ ∷ A) ⦃ idp ⦄ = υ A

      _,,₊_ : ∀ Γ {A : Ty Γ} → Tm A → Sub Γ (Γ ∷ A)
      Γ ,,₊ a = id ,, a [ id ]ₜ

    module term-coercions {Γ : Con} where
      coeᵀᵐ-∙ : {A B C : Ty Γ} {t : Tm A} (p : A == B) (q : B == C)
                → coeᵀᵐ (p ∙ q) t == coeᵀᵐ q (coeᵀᵐ p t)
      coeᵀᵐ-∙ idp q = idp

      coeᵀᵐ-∙! : {A B C : Ty Γ} {t : Tm A} (p : A == B) (q : B == C)
                 → coeᵀᵐ q (coeᵀᵐ p t) == coeᵀᵐ (p ∙ q) t
      coeᵀᵐ-∙! p q = ! (coeᵀᵐ-∙ p q)

      coe!ᵀᵐ-∙ : {A B C : Ty Γ} {t : Tm C} (p : A == B) (q : B == C)
                 → coe!ᵀᵐ (p ∙ q) t == coe!ᵀᵐ p (coe!ᵀᵐ q t)
      coe!ᵀᵐ-∙ idp q = idp

      coe!ᵀᵐ-∙! : {A B C : Ty Γ} {t : Tm C} (p : A == B) (q : B == C)
                  → coe!ᵀᵐ p (coe!ᵀᵐ q t) == coe!ᵀᵐ (p ∙ q) t
      coe!ᵀᵐ-∙! p q = ! (coe!ᵀᵐ-∙ p q)

      -- Mediating between dependent paths and coercions
      to-coeᵀᵐˡ : {A A' : Ty Γ} {t : Tm A} {t' : Tm A'} {p : A == A'}
                  → t == t' over⟨ p ⟩
                  → coeᵀᵐ p t == t'
      to-coeᵀᵐˡ {t = t} {t'} {idp} = idf (t == t')

      to-coeᵀᵐʳ : {A A' : Ty Γ} {t : Tm A} {t' : Tm A'} {p : A == A'}
                  → t == t' over⟨ p ⟩
                  → t == coe!ᵀᵐ p t'
      to-coeᵀᵐʳ {t = t} {t'} {idp} = idf (t == t')

      from-coeᵀᵐˡ : {A A' : Ty Γ} {t : Tm A} {t' : Tm A'} {p : A == A'}
                  → coeᵀᵐ p t == t'
                  → t == t' over⟨ p ⟩
      from-coeᵀᵐˡ {t = t} {t'} {idp} = idf (t == t')

      from-over-∙ :
        {A B C : Ty Γ} {p : A == B} {q : B == C}
        {a : Tm A} {c : Tm C}
        → a == c over⟨ p ∙ q ⟩
        → coeᵀᵐ p a == c over⟨ q ⟩
      from-over-∙ {p = idp} = idf _

      to-over-∙ :
        {A B C : Ty Γ} {p : A == B} {q : B == C}
        {a : Tm A} {c : Tm C}
        → coeᵀᵐ p a == c over⟨ q ⟩
        → a == c over⟨ p ∙ q ⟩
      to-over-∙ {p = idp} = idf _

  open notation public
  open term-coercions public

  private
    module equalities where
      βυ' : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
            → υ A [ f ,, t ]ₜ == coeᵀᵐ (! [= βπ ] ∙ [◦]) t
      βυ' {t = t} =
        to-transp' βυ
        ∙ ap (λ p → coeᵀᵐ p t)
             (!-∙ ![◦] [= βπ ]
             ∙ ap (! [= βπ ] ∙_) (!-! _))

      -- Important lemma; substitution of transported terms
      coeᵀᵐ-[]ₜ-stable :
        ∀ {Γ Δ} {A A' : Ty Δ} (p : A == A') (a : Tm A) (f : Sub Γ Δ)
        → a [ f ]ₜ == (coeᵀᵐ p a) [ f ]ₜ over⟨ p |in-ctx _[ f ] ⟩
      coeᵀᵐ-[]ₜ-stable idp a f = idp

      coeᵀᵐ[]ₜ : ∀ {Γ Δ} {A A' : Ty Δ} (p : A == A') (a : Tm A) (f : Sub Γ Δ)
        → (coeᵀᵐ p a) [ f ]ₜ == coeᵀᵐ (p ⁼[ f ]) (a [ f ]ₜ)
      coeᵀᵐ[]ₜ idp _ _ = idp

      υ-,, : ∀ {Γ} (A : Ty Γ) (a : Tm A)
             → υ A [ Γ ,,₊ a ]ₜ == a [ π A ]ₜ [ Γ ,,₊ a ]ₜ
      υ-,, {Γ} A a =
        υ A [ Γ ,,₊ a ]ₜ
          =⟨ βυ ⟫ᵈ
        a [ id ]ₜ
          =⟨ !ᵈ [= βπ ]ₜ ∙ᵈ [◦]ₜ ⟩ᵈ
        a [ π A ]ₜ [ Γ ,,₊ a ]ₜ
          =∎↓⟨ <!∙>∙!∙ [◦] [= βπ ] ⟩

      {- Equality of substitutions

      An equality of extended substitutions is a pair consisting of an equality
      between the first substitutions and a dependent path between the extending
      elements.
      -}
      ⟨=_,,_=⟩ :
        ∀ {Γ Δ} {A : Ty Δ} {f f' : Sub Γ Δ} {t : Tm (A [ f ])} {t' : Tm (A [ f' ])}
        → (p : f == f')
        → t == t' over⟨ [= p ] ⟩
        → (f ,, t ) == (f' ,, t')
      ⟨= idp ,, idp =⟩ = idp

      ⟨=,,_=⟩ :
        ∀ {Γ Δ} {A : Ty Δ} {f : Sub Γ Δ} {t t' : Tm (A [ f ])}
        → t == t'
        → (f ,, t ) == (f ,, t')
      ⟨=,, idp =⟩ = idp

      ⟨=_,,=⟩ :
        ∀ {Γ Δ} {A : Ty Δ} {f f' : Sub Γ Δ} {t : Tm (A [ f ])}
        → (p : f == f')
        → (f ,, t) == (f' ,, coeᵀᵐ [= p ] t)
      ⟨= idp ,,=⟩ = idp

      η-sub : ∀ {Γ Δ} {A : Ty Δ} (ϕ : Sub Γ (Δ ∷ A))
              → ϕ == (π A ◦ ϕ ,, coe!ᵀᵐ [◦] (υ A [ ϕ ]ₜ))
      η-sub {A = A} ϕ =
        ϕ
          =⟨ ! (idl ϕ) ⟩
        id ◦ ϕ
          =⟨ ! η,, |in-ctx (_◦ ϕ) ⟩
        (π A ,, υ A) ◦ ϕ
          =⟨ ,,-◦ ⟩
        (π A ◦ ϕ ,, coe!ᵀᵐ [◦] (υ A [ ϕ ]ₜ) )
          =∎

      sub= : ∀ {Γ Δ} {A : Ty Δ} (f g : Sub Γ (Δ ∷ A))
        → (p : π A ◦ f == π A ◦ g)
        → coe!ᵀᵐ [◦] (υ A [ f ]ₜ) == coe!ᵀᵐ [◦] (υ A [ g ]ₜ) over⟨ [= p ] ⟩
        → f == g
      sub= {A = A} f g p q = η-sub f ∙ ⟨= p ,, q =⟩ ∙ ! (η-sub g)

      -- Characterization of substitutions into extended contexts
      module _ {Γ Δ : Con} {A : Ty Δ} where
        ext-sub-equiv :
          Sub Γ (Δ ∷ A) ≃ (Σ[ σ ﹕ Sub Γ Δ ] Tm (A [ σ ]))
        ext-sub-equiv =
          equiv f g h1 h2
          where
          f = λ σ → (π A ◦ σ) , coe!ᵀᵐ [◦] (υ A [ σ ]ₜ)
          g = uncurry _,,_
          h2 = ! ∘ η-sub

          lem : ∀ σ a
              → transp (Tm ∘ (A [_])) βπ
                  (coe!ᵀᵐ [◦] (υ A [ σ ,, a ]ₜ))
                == a
          lem σ a =
            (! (ap[=] βπ)
            |in-ctx (λ ◻ → coe ◻ (coe!ᵀᵐ [◦] (υ A [ σ ,, a ]ₜ)))
            )
            ∙ ! (transp-∙ ![◦] [= βπ ] (υ A [ σ ,, a ]ₜ))
            ∙ to-transp βυ

          h1 = λ{(σ , a) → pair= βπ (from-transp _ βπ (lem σ a))}

      ext-sub-elim : ∀ {ℓ} {Γ Δ} {A : Ty Δ} (P : Sub Γ (Δ ∷ A) → Type ℓ)
        → ((f : Sub Γ Δ) (t : Tm (A [ f ])) → P (f ,, t))
        → (f : Sub Γ (Δ ∷ A)) → P f
      ext-sub-elim {A = A} P m f =
        transp P (! (η-sub f)) $ m (π A ◦ f) (coe!ᵀᵐ [◦] (υ A [ f ]ₜ))

      ext-sub-rec : ∀ {ℓ} {Γ Δ} {A : Ty Δ} {B : Type ℓ}
        → ((f : Sub Γ Δ) (t : Tm (A [ f ])) → B)
        → (f : Sub Γ (Δ ∷ A)) → B
      ext-sub-rec {ℓ} {Γ} {Δ} {A} {B} = ext-sub-elim {ℓ} {Γ} {Δ} {A} (λ _ → B)

      -- Commutativity properties
      [=]-[◦]-comm :
        ∀ {Γ Δ Ε} {f f' : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε}
        → (p : f == f')
        → [◦] {A = A} ∙ [= p ] == [= ap (g ◦_) p ] ∙ [◦]
      [=]-[◦]-comm idp = ∙-unit-r [◦]

  open equalities public

  private
    module universal-properties where

      ,,-uniq : ∀ {Γ Δ} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
                  (ϕ : Sub Γ (Δ ∷ A))
                  (πϕ : π A ◦ ϕ == f)
                  (υϕ : υ A [ ϕ ]ₜ == t over⟨ (! [◦] ∙ [= πϕ ]) ⟩)
                → ϕ == (f ,, t)
      ,,-uniq {f = f} {A} {t} ϕ πϕ υϕ =
        ϕ
          =⟨ ! (idl ϕ) ⟩
        id ◦ ϕ
          =⟨ ! η,, |in-ctx (_◦ ϕ) ⟩
        (π A ,, υ A) ◦ ϕ
          =⟨ ,,-◦ ⟩
        (π A ◦ ϕ ,, coe!ᵀᵐ [◦] (υ A [ ϕ ]ₜ) )
          =⟨ ⟨= πϕ ,, from-over-∙ υϕ =⟩ ⟩
        (f ,, t)
          =∎

  open universal-properties public

  private
    module extension {Γ Δ : Con} where

      {- Given f : Sub Γ Δ and A : Ty Δ, we get the weakening (f ∷ₛ A) of f by A
      that, intuitively, acts as f does, and leaves the "last term a : A[f]"
      alone. This diagram commutes:

                            f ∷ₛ A
                   Γ ∷ A[f] -----> Δ ∷ A
            π (A[f]) |               | π A    (*)
                     ↓               ↓
                     Γ ------------> Δ
                             f
      -}

      infixl 40 _∷ₛ_
      _∷ₛ_ : (f : Sub Γ Δ) (A : Ty Δ) → Sub (Γ ∷ A [ f ]) (Δ ∷ A)
      f ∷ₛ A = f ◦ π (A [ f ]) ,, coe!ᵀᵐ [◦] (υ (A [ f ]))

      ∷ₛ-comm : {A : Ty Δ} {f : Sub Γ Δ} → π A ◦ (f ∷ₛ A) == f ◦ π (A [ f ])
      ∷ₛ-comm = βπ

      {- Given f and A as in (*) above and a : Tm A, we have (Γ ,,₊ a) := (id ,, a[id]ₜ)
      and the two compositions forming the boundary of the square below:

                            f ∷ₛ A
                   Γ ∷ A[f] -----> Δ ∷ A
          Γ ,,₊ a[f] ↑               ↑ Δ ,,₊ a    (**)
                     |               |
                     Γ ------------> Δ
                             f

      There is also a direct substitution on the diagonal, which is (f ,, a[f]ₜ).
      We show that the two compositions are each equal to the diagonal, which implies
      that the compositions are equal.

      The first is easy: -}

      ,,₊-◦ : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
              → (Δ ,,₊ a) ◦ f == (f ,, a [ f ]ₜ)
      ,,₊-◦ f a =
        (Δ ,,₊ a) ◦ f
          =⟨ ,,-◦ ⟩        (id ◦ f ,, coe!ᵀᵐ [◦] (a [ id ]ₜ [ f ]ₜ))
          =⟨ ⟨= (idl f) ,, from-over-∙ (!ᵈ [◦]ₜ ∙ᵈ [= idl f ]ₜ) =⟩ ⟩
        (f ,, a [ f ]ₜ)
          =∎

      {- The second is a bit more work. We use the universal property ,,-uniq and
      prove a series of somewhat lengthy reductions.

      COMMENT 2023-08-09: Can this proof be simplified using sub= instead? -}

      -- In (**), going up, left and then down (by π) is the same as f.
      ⊓-lemma : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
                → π A ◦ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) == f
      ⊓-lemma f a = ! ass
                    ∙ (∷ₛ-comm |in-ctx (_◦ (Γ ,,₊ a [ f ]ₜ)))
                    ∙ ass
                    ∙ (βπ |in-ctx (f ◦_))
                    ∙ idr f

      ∷ₛ-,,₊ : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
              → (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) == (f ,, a [ f ]ₜ)
      ∷ₛ-,,₊ {A} f a = ,,-uniq ((f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ)) (⊓-lemma f a) (red1 ∙ᵈ red2)
        where
        calc : υ A [ f ∷ₛ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
              == a [ π A ]ₜ [ f ∷ₛ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
        calc =
          υ A [ f ∷ₛ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟫ᵈ
          coe!ᵀᵐ [◦] (υ (A [ f ])) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ (coeᵀᵐ-[]ₜ-stable (! [◦]) (υ (A [ f ])) (Γ ,,₊ a [ f ]ₜ)) ⟫ᵈ
          υ (A [ f ]) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ υ-,, (A [ f ]) (a [ f ]ₜ) ⟫ᵈ
          a [ f ]ₜ [ π (A [ f ]) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [◦]ₜ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟫ᵈ
          a [ f ◦ π (A [ f ]) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [= ∷ₛ-comm ]ₜ ∙ᵈ [◦]ₜ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟩ᵈ
          a [ π A ]ₜ [ f ∷ₛ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =∎↓⟨ =ₛ-out base-paths-equal ⟩
          where
            base-paths-equal :
              (! [◦] ∙ [= βπ ] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∙
              ! (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∙
              (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∙
              (! [= βπ ] ∙ [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ◃∎
              =ₛ idp ◃∎
            base-paths-equal =
              (! [◦] ∙ [= βπ ] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ ! (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ (! [= βπ ] ∙ [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∎
                =ₛ₁⟨ 1 & 2 & !-inv-l (! [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ]) ⟩

              (! [◦] ∙ [= βπ ] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∙ idp
              ◃∙ (! [= βπ ] ∙ [◦] |in-ctx _[ Γ ,,₊ (a [ f ]ₜ) ])
              ◃∎
                =ₛ₁⟨ ! (ap-∙ _[ Γ ,,₊ (a [ f ]ₜ) ] (! [◦] ∙ [= βπ ]) (! [= βπ ] ∙ [◦]))
                   ∙ (<!∙>∙!∙ [◦] [= βπ ] |in-ctx (ap _[ Γ ,,₊ a [ f ]ₜ ])) ⟩

              idp ◃∎ ∎ₛ

        red1 : υ A [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
               == a [ π A ]ₜ [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
        red1 =
          υ A [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =⟨ [◦]ₜ ↓ [◦] ⟫ᵈ
          υ A [ f ∷ₛ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ calc ⟫ᵈ
          a [ π A ]ₜ [ f ∷ₛ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [◦]ₜ ↓ ! [◦] ⟩ᵈ
          a [ π A ]ₜ [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =∎↓⟨ !-inv-r [◦] ⟩

        red2 : a [ π A ]ₜ [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ == a [ f ]ₜ
                 over⟨ ! [◦] ∙ [= ⊓-lemma f a ] ⟩
        red2 = !ᵈ [◦]ₜ ∙ᵈ [= ⊓-lemma f a ]ₜ

        {- Failed attempt; just some random path in the total space may not lie over
        the path we want in the base:

        wrong : υ A [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ == a [ f ]ₜ
                       over⟨ ! [◦] ∙ [= ⊓-lemma f a ] ⟩
        wrong =
          υ A [ (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =⟨ [◦]ₜ ↓ [◦] ⟫ᵈ
          υ A [ f ◦ π (A [ f ]) ,, coe!ᵀᵐ [◦] (υ (A [ f ])) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ |in-ctx↓ᵀᵐ (_[ Γ ,,₊ a [ f ]ₜ ]ₜ) ⟫ᵈ
          coe!ᵀᵐ [◦] (υ (A [ f ])) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ (coeᵀᵐ-,,-stable (! [◦]) (υ (A [ f ])) id (a [ f ]ₜ [ id ]ₜ)) ⟫ᵈ
          υ (A [ f ]) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ ⟫ᵈ
          a [ f ]ₜ [ id ]ₜ
            =⟨ !ᵈ [◦]ₜ ∙ᵈ [= idr ]ₜ ⟩ᵈ
          a [ f ]ₜ
            =∎↓⟨ {!!} ⟩ -}

      ,,₊-comm : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
                 → (Δ ,,₊ a) ◦ f == (f ∷ₛ A) ◦ (Γ ,,₊ a [ f ]ₜ)
      ,,₊-comm f a = ,,₊-◦ f a ∙ ! (∷ₛ-,,₊ f a)

  open extension public

  private
    module substitutions where
      infix 40 _⟦_⟧ _⟦_⟧ₜ

      _⟦_⟧ : ∀ {Γ} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
      _⟦_⟧ {Γ} B a = B [ Γ ,,₊ a ]

      _⟦_⟧ₜ : ∀ {Γ} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A) → Tm (B ⟦ a ⟧)
      _⟦_⟧ₜ {Γ} b a = b [ Γ ,,₊ a ]ₜ

      -- Commutation law
      []-⟦⟧ : ∀ {Γ Δ} {A : Ty Δ} (B : Ty (Δ ∷ A)) (f : Sub Γ Δ) (a : Tm A)
              → B [ f ∷ₛ A ] ⟦ a [ f ]ₜ ⟧ == B ⟦ a ⟧ [ f ]
      []-⟦⟧ B f a = ! [◦] ∙ ! [= ,,₊-comm f a ] ∙ [◦]

      -- Coercing to equal substitutions
      coe-cod : ∀ {Γ Δ Δ'} → Δ == Δ' → Sub Γ Δ → Sub Γ Δ'
      coe-cod idp = idf _

      -- Important; comment on it later
      module _ {Γ Δ Ε} (A : Ty Ε) (σ : Sub Δ Ε) (τ : Sub Γ Δ) where
        id-sub-◦ : Sub (Γ ∷ A [ σ ◦ τ ]) (Γ ∷ A [ σ ] [ τ ])
        id-sub-◦ = let X = A [ σ ◦ τ ] in
          π X ,, coeᵀᵐ (ap (_[ π X ]) [◦]) (υ X)

        id-sub-!◦ : Sub (Γ ∷ A [ σ ] [ τ ]) (Γ ∷ A [ σ ◦ τ ])
        id-sub-!◦ = let X = A [ σ ] [ τ ] in
          π X ,, coeᵀᵐ (ap (_[ π X ]) ![◦]) (υ X)

        -- _ : id-sub-!◦ ◦ id-sub-◦ == id
        -- _ = id-sub-!◦ ◦ id-sub-◦
        --   =⟨ ,,-◦ ⟩
        --   {!!}
        --   =⟨ ⟨= βπ ,,=⟩ ⟩
        --   {!!}
        --   =⟨ {!!} ⟩
        --   id
        --   =∎

  open substitutions public

  private
    module terms-and-sections {Γ} (A : Ty Γ) where
      -- Should maybe reorganize this file and put this module somewhere earlier

      _`[id]ₜ : Tm A → Tm (A [ id ])
      a `[id]ₜ = a [ id ]ₜ

      `[id]ₜ=transp : _`[id]ₜ == transp! Tm [id]
      `[id]ₜ=transp = λ= (λ a → to-transp' [id]ₜ)

      `[id]ₜ-is-equiv : is-equiv _`[id]ₜ
      `[id]ₜ-is-equiv =
        transp is-equiv (! `[id]ₜ=transp) (transp-is-equiv Tm (! [id]))

      `[id]ₜ-equiv : Tm A ≃ Tm (A [ id ])
      `[id]ₜ-equiv = _`[id]ₜ , `[id]ₜ-is-equiv

      section≃Tm : (Σ[ σ ﹕ Sub Γ (Γ ∷ A) ] π A ◦ σ == id) ≃ Tm A
      section≃Tm =
        Σ[ σ ﹕ Sub Γ (Γ ∷ A) ] π A ◦ σ == id
          ≃⟨ Σ-emape-dom _ ext-sub-equiv ⟩
        Σ[ u ﹕ Σ[ σ ﹕ Sub Γ Γ ] Tm (A [ σ ]) ] π A ◦ (fst u ,, snd u) == id
          ≃⟨ Σ-emap-r (λ u → (pre∙-equiv βπ) ⁻¹) ⟩
        Σ[ u ﹕ Σ[ σ ﹕ Sub Γ Γ ] Tm (A [ σ ]) ] fst u == id
          ≃⟨ Σ₂-×-comm ⟩
        Σ[ u ﹕ Σ[ σ ﹕ Sub Γ Γ ] σ == id ] Tm (A [ fst u ])
          ≃⟨ Σ-contr-dom (pathto-is-contr id) ⟩
        Tm (A [ id ])
          ≃⟨ `[id]ₜ-equiv ⁻¹ ⟩
        Tm A ≃∎

      module section→tm (a : Tm A) where
        sect-from-a = <– section≃Tm a

        sect-from-a-val : sect-from-a == (id ,, a [ id ]ₜ) , βπ ∙ idp
        sect-from-a-val = idp

        -- The equivalence between sections and terms constructed above has the
        -- map a ↦ (id ,, a [ id ]ₜ) as the term → section map (the witness of
        -- commutativity is just Βπ).
        sect-from-a-val' : sect-from-a == (Γ ,,₊ a) , βπ
        sect-from-a-val' = pair= idp (∙-unit-r _)

      module tm→section (σ : Sub Γ (Γ ∷ A)) (s : π A ◦ σ == id) where
        -- For now, we don't care about the normal form of the section → term
        -- map of the equivalence.
        -- tm-from-sect = {!–> (section≃Tm) (σ , s) -- C-c C-n ???!}
