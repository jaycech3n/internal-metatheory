{-# OPTIONS --without-K --rewriting #-}

-- This is a bundled version of cwfs.Contextual, where Con is indexed over lengths.

module cwfs.contextual.CwFs where

open import categories.Categories public

{-
record ᵂContextualCwF ℓₒ ℓₘ : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  infixl 31 _∷_
  infixl 35 _,,_
  infixl 40 _[_] _[_]ₜ

  -- Category of contexts, graded by context length
  field 𝒞 : ᴳᵂCategory _ ℓₒ ℓₘ ℕ
  open ᴳᵂCategory 𝒞 renaming (Ob to Con; hom to Sub) public

  field
    -- Empty context
    ◆ : Con O
    ◆-terminal : ∀ {n} (Γ : Con n) → is-contr (Sub Γ ◆)

    -- Types, terms, substitution
    Ty   : ∀ {n} → Con n → Type ℓₒ
    _[_] : ∀ {m n} {Γ : Con m} {Δ : Con n} → Ty Δ → Sub Γ Δ → Ty Γ
    [id] : ∀ {n} {Γ : Con n} {A : Ty Γ} → A [ id ] == A
    [◦]  : ∀ {m n k} {Γ : Con m} {Δ : Con n} {Ε : Con k}
           {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} -- Greek capital epsilon, \GE
           → A [ g ◦ f ] == A [ g ] [ f ]

    Tm    : ∀ {n} {Γ : Con n} → Ty Γ → Type ℓₘ
    _[_]ₜ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A : Ty Δ}
            → Tm A → (f : Sub Γ Δ) → Tm (A [ f ])
    [id]ₜ : ∀ {n} {Γ : Con n} {A : Ty Γ} {t : Tm A}
            → t [ id ]ₜ == t [ Tm ↓ [id] ]
    [◦]ₜ  : ∀ {m n k} {Γ : Con m} {Δ : Con n} {Ε : Con k}
            {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm A}
            → t [ g ◦ f ]ₜ == t [ g ]ₜ [ f ]ₜ [ Tm ↓ [◦] ]

    -- Comprehension
    _∷_  : ∀ {n} (Γ : Con n) → Ty Γ → Con (1+ n)
    π    : ∀ {n} {Γ : Con n} (A : Ty Γ) → Sub (Γ ∷ A) Γ
    υ    : ∀ {n} {Γ : Con n} (A : Ty Γ) → Tm (A [ π A ])
    _,,_ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A : Ty Δ}
           → (f : Sub Γ Δ) (t : Tm (A [ f ])) → Sub Γ (Δ ∷ A)

    βπ : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ}
         {A : Ty Δ} {t : Tm (A [ f ])}
         → π A ◦ (f ,, t) == f

    βυ : ∀ {m n} {Γ : Con m} {Δ : Con n}
         {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
         → υ A [ f ,, t ]ₜ == t [ Tm ↓ ! [◦] ∙ ap (A [_]) βπ ]

    η,, : ∀ {n} {Γ : Con n} {A : Ty Γ} → (π A ,, υ A) == id

    ,,-◦ : ∀ {m n k} {Γ : Con m} {Δ : Con n} {Ε : Con k}
           {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε} {t : Tm (A [ g ])}
           → (g ,, t) ◦ f == (g ◦ f ,, transp Tm (! [◦]) (t [ f ]ₜ))

    -- Contextuality
    instance Con-O : is-contr (Con O)
    Con-S : ∀ {n} → is-equiv (uncurry (_∷_ {n}))

  private
    module notation where
      PathOver-Tm :
        ∀ {n} {Γ : Con n} {A A' : Ty Γ}
          (p : A == A') (t : Tm A) (t' : Tm A')
        → Type ℓₘ
      PathOver-Tm = PathOver Tm

      syntax PathOver-Tm p t t' = t == t' over⟨ p ⟩

      ![◦] :
        ∀ {l m n} {Γ : Con l} {Δ : Con m} {Ε : Con n}
          {f : Sub Γ Δ} {g : Sub Δ Ε} {A : Ty Ε}
        → A [ g ] [ f ] == A [ g ◦ f ]
      ![◦] = ! [◦]

      [=_] :
        ∀ {m n} {Γ : Con m} {Δ : Con n}
          {f f' : Sub Γ Δ} {A : Ty Δ}
        → f == f' → A [ f ] == A [ f' ]
      [=_] {A = A} = ap (A [_])

      [=_]ₜ :
        ∀ {m n} {Γ : Con m} {Δ : Con n}
          {f f' : Sub Γ Δ} {A : Ty Δ} {t : Tm A} (p : f == f')
        → t [ f ]ₜ == t [ f' ]ₜ over⟨ [= p ] ⟩
      [= idp ]ₜ = idp

      infixl 40 ap↓-Tm
      ap↓-Tm : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Ty Γ → Ty Δ}
          (g : {A : Ty Γ} → Tm A → Tm (f A))
          {A A' : Ty Γ} {p : A == A'}
          {a : Tm A} {a' : Tm A'}
        → a == a' [ Tm ↓ p ]
        → g a == g a' [ Tm ↓ ap f p ]
      ap↓-Tm = ap↓3 {A = ℕ} {B = Con} {C = Ty} {D = Tm}

      syntax ap↓-Tm g q = q |in-ctx↓ᵀᵐ g

      Tm[_] : ∀ {n} (Γ : Con n) → Ty Γ → Type ℓₘ
      Tm[ Γ ] A = Tm A

      _ʷ : ∀ {n} {Γ : Con n} {A : Ty Γ} → Ty Γ → Ty (Γ ∷ A)
      _ʷ {A = A} B = B [ π A ]

      _ʷₜ : ∀ {n} {Γ : Con n} {A B : Ty Γ} → Tm B → Tm (B [ π A ])
      _ʷₜ {A = A} b = b [ π A ]ₜ

      instance
        witness-∷ : ∀ {n} {Γ : Con n} {A : Ty Γ} → Γ ∷ A == Γ ∷ A
        witness-∷ = idp

      var : ∀ {n} {Γ : Con n} {A : Ty Γ} (Δ : Con (1+ n))
            → ⦃ Δ == Γ ∷ A ⦄ → Tm[ Γ ∷ A ] (A ʷ)
      var {Γ = Γ} {A} .(Γ ∷ A) ⦃ idp ⦄ = υ A

  open notation public

  private
    module contexts where
      ext : ∀ {n} → Σ (Con n) Ty → Con (1+ n)
      ext {n} = uncurry (_∷_ {n})

      split : ∀ {n} → Con (1+ n) → Σ (Con n) Ty
      split = inv-equiv Con-S

      mutual
        Conᶜ : ℕ → Type ℓₒ
        con-of : ∀ {n} → Conᶜ n → Con n

        Conᶜ O = Lift ⊤
        Conᶜ (1+ n) = Σ (Conᶜ n) (Ty ∘ con-of)

        con-of {O} _ = ◆
        con-of {1+ n} = ext ∘ Σ-fmap-l _ con-of
          -- this is just (Γᶜ , A) ↦ con-of Γᶜ ∷ A

      con-of-is-equiv : ∀ n → is-equiv (con-of {n})
      con-of-is-equiv O = is-eq _ _
        (contr-has-all-paths _) (contr-has-all-paths _)
      con-of-is-equiv (1+ n) = Con-S ∘ise Σ-isemap-l _ (con-of-is-equiv n)

      Tyᶜ : ∀ {n} → Conᶜ n → Type ℓₒ
      Tyᶜ = Ty ∘ con-of

      Subᶜ : ∀ {m n} → Conᶜ m → Conᶜ n → Type ℓₘ
      Subᶜ {n = O} _ _ = Lift ⊤
      Subᶜ {n = 1+ n} Γᶜ (Δᶜ , A) = {!!}

      -- code-of : ∀ {n} → Con n → Conᶜ n
      -- code-of {O} _ = lift unit
      -- code-of {1+ n} Γ = Σ-fmap-l _ code-of {!split Γ!}

  private
    module context-operations where
      empty : (Γ : Con O) → Γ == ◆
      empty Γ = contr-has-all-paths ⦃ Con-O ⦄ Γ ◆

      dest : ∀ {n} → Con (1+ n) → Σ[ Δ ː Con n ] Ty Δ
      dest = inv-equiv Con-S

      dest= : ∀ {n} (Γ : Con (1+ n)) → fst (dest Γ) ∷ snd (dest Γ) == Γ
      dest= Γ = <–-inv-r (uncurry _∷_ , Con-S) Γ

      abstract
        Con-case : ∀ {ℓ}
          → (P : ∀ {n} → Con n → Type ℓ)
          → P ◆
          → (∀ {n} (Γ : Con n) (A : Ty Γ) → P (Γ ∷ A))
          → ∀ {n} (Γ : Con n) → P Γ
        Con-case _ P◆ _ {n = O} Γ rewrite empty Γ = P◆
        Con-case P _ P∷ {1+ n} Γ = transp P (dest= Γ) (uncurry P∷ $ dest Γ)

  open context-operations public

  module extension where
    _,,₊_ : ∀ {n} (Γ : Con n) {A : Ty Γ} → Tm A → Sub Γ (Γ ∷ A)
    Γ ,,₊ a = id ,, a [ id ]ₜ

  module term-coercions {n} {Γ : Con n} where
    -- Coercing terms to equal terms in equal types
    coeᵀᵐ : {A A' : Ty Γ} → A == A' → Tm A → Tm A'
    coeᵀᵐ p = coe (ap Tm p) -- coeᵀᵐ {A = A} idp = idf (Tm A)

    coe!ᵀᵐ : {A A' : Ty Γ} → A == A' → Tm A' → Tm A
    coe!ᵀᵐ p = coeᵀᵐ (! p)

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
      → a == c over⟨ p ∙ q ⟩ → coeᵀᵐ p a == c over⟨ q ⟩
    from-over-∙ {p = idp} = idf _

  open extension public
  open term-coercions public

  private
    module equalities where
      -- An equality of extended substitutions is a pair consisting of an equality
      -- between the first substitutions and a dependent path between the extending
      -- elements.
      ⟨=_,,_=⟩ : ∀ {m n} {Γ : Con m} {Δ : Con n}
          {A : Ty Δ} {f f' : Sub Γ Δ} {t : Tm (A [ f ])} {t' : Tm (A [ f' ])}
        → (p : f == f')
        → t == t' over⟨ [= p ] ⟩
        → (f ,, t ) == (f' ,, t')
      ⟨= idp ,, idp =⟩ = idp

      ⟨=,,_=⟩ : ∀ {m n} {Γ : Con m} {Δ : Con n}
          {A : Ty Δ} {f : Sub Γ Δ} {t t' : Tm (A [ f ])}
        → t == t'
        → (f ,, t ) == (f ,, t')
      ⟨=,, idp =⟩ = idp

      ⟨=_,,=⟩ : ∀ {m n} {Γ : Con m} {Δ : Con n}
          {A : Ty Δ} {f f' : Sub Γ Δ} {t : Tm (A [ f ])}
        → (p : f == f')
        → (f ,, t ) == (f' ,, coeᵀᵐ [= p ] t)
      ⟨= idp ,,=⟩ = idp

      υ-,, : ∀ {n} {Γ : Con n} (A : Ty Γ) (a : Tm A)
             → υ A [ Γ ,,₊ a ]ₜ == a [ π A ]ₜ [ Γ ,,₊ a ]ₜ
      υ-,, {Γ = Γ} A a =
        υ A [ Γ ,,₊ a ]ₜ
          =⟨ βυ ⟫ᵈ
        a [ id ]ₜ
          =⟨ !ᵈ [= βπ ]ₜ ∙ᵈ [◦]ₜ ⟩ᵈ
        a [ π A ]ₜ [ Γ ,,₊ a ]ₜ
          =∎↓⟨ <!∙>∙!∙ [◦] [= βπ ] ⟩

      -- Important lemma: coercions along equalities of hypothetical/weakened elements
      -- are stable under substitution by _,,_.
      coeᵀᵐ-,,-stable :
        ∀ {m n} {Γ : Con m} {Δ : Con n} {A : Ty Δ} {A' : Ty (Δ ∷ A)}
          (p : A [ π A ] == A') (x : Tm (A [ π A ])) (f : Sub Γ Δ) (t : Tm (A [ f ]))
        → x [ f ,, t ]ₜ == (coeᵀᵐ p x) [ f ,, t ]ₜ over⟨ p |in-ctx (_[ f ,, t ]) ⟩
      coeᵀᵐ-,,-stable idp x f t = idp

  open equalities public

  private
    module universal-properties where

      ,,-uniq : ∀ {m n} {Γ : Con m} {Δ : Con n} {f : Sub Γ Δ} {A : Ty Δ} {t : Tm (A [ f ])}
                  (ϕ : Sub Γ (Δ ∷ A))
                  (πϕ : π A ◦ ϕ == f)
                  (υϕ : υ A [ ϕ ]ₜ == t over⟨ (! [◦] ∙ [= πϕ ]) ⟩)
                → ϕ == (f ,, t)
      ,,-uniq {f = f} {A} {t} ϕ πϕ υϕ =
        ϕ
          =⟨ ! idl ⟩
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
    module weakening {m n} {Γ : Con m} {Δ : Con n} where

      {- Given f : Sub Δ Γ and A : Ty Γ, we get the weakening (f ↑ A) of f by A that,
      intuitively, acts as f does, and leaves the "free variable x : A" alone. This
      diagram commutes:

                            f ↑ A
                   Γ ∷ A[f] -----> Δ ∷ A
            π (A[f]) |               | π A    (*)
                     ↓               ↓
                     Γ ------------> Δ
                             f
      -}

      _↑_ : (f : Sub Γ Δ) (A : Ty Δ) → Sub (Γ ∷ A [ f ]) (Δ ∷ A)
      f ↑ A = f ◦ π (A [ f ]) ,, coe!ᵀᵐ [◦] (υ (A [ f ]))

      ↑-comm : {A : Ty Δ} {f : Sub Γ Δ} → π A ◦ (f ↑ A) == f ◦ π (A [ f ])
      ↑-comm = βπ

      {- Given f and A as in (*) above and a : Tm A, we have (Γ ,,₊ a) := (id ,, a[id]ₜ)
      and the two compositions forming the boundary of the square below:

                            f ↑ A
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
          =⟨ ,,-◦ ⟩
        (id ◦ f ,, coe!ᵀᵐ [◦] (a [ id ]ₜ [ f ]ₜ))
          =⟨ ⟨= idl ,, from-over-∙ (!ᵈ [◦]ₜ ∙ᵈ [= idl ]ₜ) =⟩ ⟩
        (f ,, a [ f ]ₜ)
          =∎

      {- The second is a bit more work. We use the universal property ,,-uniq and
      prove a series of somewhat lengthy reductions. -}

      -- In (**), going up, left and then down (by π) is the same as f.
      ⊓-lemma : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
                → π A ◦ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) == f
      ⊓-lemma f a = ! ass
                    ∙ (↑-comm |in-ctx (_◦ (Γ ,,₊ a [ f ]ₜ)))
                    ∙ ass
                    ∙ (βπ |in-ctx (f ◦_))
                    ∙ idr

      ↑-,,₊ : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
              → (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) == (f ,, a [ f ]ₜ)
      ↑-,,₊ {A} f a = ,,-uniq ((f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ)) (⊓-lemma f a) (red1 ∙ᵈ red2)
        where
        calc : υ A [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
              == a [ π A ]ₜ [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
        calc =
          υ A [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ βυ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟫ᵈ
          coe!ᵀᵐ [◦] (υ (A [ f ])) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ (coeᵀᵐ-,,-stable (! [◦]) (υ (A [ f ])) id (a [ f ]ₜ [ id ]ₜ)) ⟫ᵈ
          υ (A [ f ]) [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ υ-,, (A [ f ]) (a [ f ]ₜ) ⟫ᵈ
          a [ f ]ₜ [ π (A [ f ]) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [◦]ₜ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟫ᵈ
          a [ f ◦ π (A [ f ]) ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [= ↑-comm ]ₜ ∙ᵈ [◦]ₜ |in-ctx↓ᵀᵐ _[ Γ ,,₊ a [ f ]ₜ ]ₜ ⟩ᵈ
          a [ π A ]ₜ [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
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

        red1 : υ A [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
               == a [ π A ]ₜ [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
        red1 =
          υ A [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =⟨ [◦]ₜ ↓ [◦] ⟫ᵈ
          υ A [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ calc ⟫ᵈ
          a [ π A ]ₜ [ f ↑ A ]ₜ [ Γ ,,₊ a [ f ]ₜ ]ₜ
            =⟨ !ᵈ [◦]ₜ ↓ ! [◦] ⟩ᵈ
          a [ π A ]ₜ [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ
            =∎↓⟨ !-inv-r [◦] ⟩

        red2 : a [ π A ]ₜ [ (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ) ]ₜ == a [ f ]ₜ
                 over⟨ ! [◦] ∙ [= ⊓-lemma f a ] ⟩
        red2 = !ᵈ [◦]ₜ ∙ᵈ [= ⊓-lemma f a ]ₜ

      ,,₊-comm : {A : Ty Δ} (f : Sub Γ Δ) (a : Tm A)
                 → (Δ ,,₊ a) ◦ f == (f ↑ A) ◦ (Γ ,,₊ a [ f ]ₜ)
      ,,₊-comm f a = ,,₊-◦ f a ∙ ! (↑-,,₊ f a)

  open weakening public

  private
    module substitutions where
      infix 40 _⟦_⟧ _⟦_⟧ₜ

      _⟦_⟧ : ∀ {n} {Γ : Con n} {A : Ty Γ} (B : Ty (Γ ∷ A)) (a : Tm A) → Ty Γ
      _⟦_⟧ {Γ = Γ} B a = B [ Γ ,,₊ a ]

      _⟦_⟧ₜ : ∀ {n} {Γ : Con n} {A : Ty Γ} {B : Ty (Γ ∷ A)} (b : Tm B) (a : Tm A)
              → Tm (B ⟦ a ⟧)
      _⟦_⟧ₜ {Γ = Γ} b a = b [ Γ ,,₊ a ]ₜ

      -- Commutation law
      []-⟦⟧ : ∀ {m n} {Γ : Con m} {Δ : Con n} {A : Ty Δ}
                (B : Ty (Δ ∷ A)) (f : Sub Γ Δ) (a : Tm A)
              → B [ f ↑ A ] ⟦ a [ f ]ₜ ⟧ == B ⟦ a ⟧ [ f ]
      []-⟦⟧ B f a = ! [◦] ∙ ! [= ,,₊-comm f a ] ∙ [◦]

      -- Coercing to equal substitutions
      coe-cod : ∀ {m n} {Γ : Con m} {Δ Δ' : Con n} → Δ == Δ' → Sub Γ Δ → Sub Γ Δ'
      coe-cod idp = idf _

  open substitutions public
-}
