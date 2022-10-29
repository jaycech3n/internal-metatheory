{-# OPTIONS --without-K #-}

open import reedy.IndexSemicategories

module reedy.LinearSieves {ℓₘ} (I : SuitableSemicategory ℓₘ) where

open SuitableSemicategory I

open import categories.DSM (SuitableSemicategory.wildsemicatstr I)

infix 90 _~[_]_ _~⋆⟨_⟩[_]_

is-[_,_,_]-admissible : (i h t : ℕ) {m : ℕ} (f : hom i m) → Type₀
is-[_,_,_]-admissible i h t f =
  (cod f < h)
  ⊔ ((cod f == h) × (to-ℕ (idx-of f) < t))

is-admissible-is-dec :
  (i h t : ℕ) {m : ℕ} (f : hom i m)
  → Dec (is-[ i , h , t ]-admissible f)
is-admissible-is-dec i h t f = ⊔-dec (_ <? _) (×-dec (_ ≟-ℕ _) (_ <? _))

admissible-next-h : ∀ i h {m} (f : hom i m)
  → is-[ i , h , hom-size i h ]-admissible f
  → is-[ i , 1+ h , O ]-admissible f
admissible-next-h i h f (inl u) = inl (ltSR u)
admissible-next-h i h f (inr (idp , _)) = inl ltS

admissible-prev-h : ∀ i h {m} (f : hom i m)
  → is-[ i , 1+ h , O ]-admissible f
  → is-[ i , h , hom-size i h ]-admissible f
admissible-prev-h i h {m} f (inl u) with ℕ-trichotomy' m h
... | inr h<m = ⊥-rec (no-between u (<-ap-S h<m))
... | inl (inl idp) = inr (idp , idx<hom-size f)
... | inl (inr m<h) = inl m<h

admissible-h-iff : ∀ i h {m} (f : hom i m)
  → to-Bool (is-admissible-is-dec i h (hom-size i h) f)
    == to-Bool (is-admissible-is-dec i (1+ h) O f)
admissible-h-iff i h f =
  ap-to-Bool
    (is-admissible-is-dec i h (hom-size i h) f)
    (is-admissible-is-dec i (1+ h) O f)
    (admissible-next-h i h f)
    (admissible-prev-h i h f)

record is-shape (i h t : ℕ) : Type₀ where
  constructor shape-conds
  field
    hcond : h ≤ i
    tcond : t ≤ hom-size i h

open is-shape

_~[_]_ : ((h₁ , t₁) : ℕ × ℕ) (i : ℕ) ((h₂ , t₂) : ℕ × ℕ)
  → ⦃ is-shape i h₁ t₁ ⦄ → ⦃ is-shape i h₂ t₂ ⦄ → Type₀
(h₁ , t₁) ~[ i ] (h₂ , t₂) = (t₁ == hom-size i h₁) × (h₂ == 1+ h₁) × (t₂ == O)

_~⋆⟨_⟩[_]_ : ((h₁ , t₁) : ℕ × ℕ) (n : ℕ) (i : ℕ) ((h₂ , t₂) : ℕ × ℕ)
  → ⦃ is-shape i h₁ t₁ ⦄ → ⦃ is-shape i h₂ t₂ ⦄ → Type₀
(h₁ , t₁) ~⋆⟨ O ⟩[ i ] (h₂ , t₂) = (h₁ , t₁) == (h₂ , t₂)
_~⋆⟨_⟩[_]_ (h₁ , t₁) (1+ n) i (h₂ , t₂) ⦃ iS₁ ⦄ ⦃ iS₂ ⦄ =
  Σ[ h ∶ ℕ ] Σ[ t ∶ ℕ ] Σ[ iS ∶ is-shape i h t ]
    _~[_]_ (h₁ , t₁) i (h , t) ⦃ iS₁ ⦄ ⦃ iS ⦄ ×
    _~⋆⟨_⟩[_]_ (h , t) n i (h₂ , t₂) ⦃ iS ⦄ ⦃ iS₂ ⦄

record LinearSieve (i : ℕ) : Type ℓₘ where
  constructor S[_,_]
  field
    height width : ℕ
    ⦃ shape-cond ⦄ : is-shape i height width
    char : DSM i
    char-∋-cond :
      ∀ {m} (f : hom i m)
      → (char ∋ f) == to-Bool (is-admissible-is-dec i height width f)

open LinearSieve

linear-sieve : ∀ i h t → is-shape i h t → LinearSieve i
linear-sieve i h t iS =
  S[ h , t ] ⦃ iS ⦄
    (λ _ f → to-Bool (is-admissible-is-dec i h t f))
    (λ _ → idp)

_~⋆⟨_⟩_ : ∀ {i} → LinearSieve i → (n : ℕ) → LinearSieve i → Type₀
_~⋆⟨_⟩_ {i} s n s' = (height s , width s) ~⋆⟨ n ⟩[ i ] (height s' , width s')

~⋆-equal-char : ∀ {n} {i} (s s' : LinearSieve i) → s ~⋆⟨ n ⟩ s' → char s == char s'
~⋆-equal-char {O} (S[ _ , _ ] χ χ-∋-cond) (S[ _ , _ ] χ' χ'-∋-cond) idp
  = DSM= (λ m f → χ-∋-cond f ∙ ! (χ'-∋-cond f))
~⋆-equal-char {1+ n} {i}
  s@(S[ h , .(hom-size i h) ] χ χ-∋-cond)
  s'@(S[ h' , t' ] χ' χ'-∋-cond)
  (.(1+ h) , .O , iS , (idp , idp , idp) , ~⋆) =
    DSM= (λ m f → χ-∋-cond f ∙ admissible-h-iff i h f)
    ∙ ~⋆-equal-char (linear-sieve i (1+ h) O iS) s' ~⋆
