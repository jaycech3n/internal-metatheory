{-# OPTIONS --without-K #-}

open import reedy.IndexSemicategories

module reedy.LinearSieves {ℓₘ} (I : SuitableSemicategory ℓₘ) where

open SuitableSemicategory I

open import categories.DSM (SuitableSemicategory.wildsemicatstr I)

{- Shapes -}

is-_-admissible : ((i , h , t) : ℕ × ℕ × ℕ) {m : ℕ} (f : hom i m) → Type₀
is-(i , h , t)-admissible f =
  (cod f < h)
  ⊔ ((cod f == h) × (to-ℕ (idx-of f) < t))

is-_-admissible? :
  ((i , h , t) : ℕ × ℕ × ℕ) {m : ℕ} (f : hom i m)
  → Dec (is-( i , h , t )-admissible f)
is- _ -admissible? f = ⊔-dec (_ <? _) (×-dec (_ ≟-ℕ _) (_ <? _))

admissible-next-h : ∀ i h {m} (f : hom i m)
  → is-( i , h , hom-size i h )-admissible f
  → is-( i , 1+ h , O )-admissible f
admissible-next-h i h f (inl u) = inl (ltSR u)
admissible-next-h i h f (inr (idp , _)) = inl ltS

admissible-prev-h : ∀ i h {m} (f : hom i m)
  → is-( i , 1+ h , O )-admissible f
  → is-( i , h , hom-size i h )-admissible f
admissible-prev-h i h {m} f (inl u) with ℕ-trichotomy' m h
... | inr h<m = ⊥-rec (no-between u (<-ap-S h<m))
... | inl (inl idp) = inr (idp , idx<hom-size f)
... | inl (inr m<h) = inl m<h

admissible-h-iff : ∀ i h {m} (f : hom i m)
  → to-Bool (is-(i , h , hom-size i h)-admissible? f)
    == to-Bool (is-(i , 1+ h , O)-admissible? f)
admissible-h-iff i h f =
  ap-to-Bool
    (is-(i , h , hom-size i h)-admissible? f)
    (is-(i , 1+ h , O)-admissible? f)
    (admissible-next-h i h f)
    (admissible-prev-h i h f)

record is-shape (i h t : ℕ) : Type₀ where
  constructor shape-conds
  field
    hcond : h ≤ i
    tcond : t ≤ hom-size i h

open is-shape

shapeₕ↓ : ∀ {i h} → is-shape i (1+ h) O → is-shape i h (hom-size i h)
shapeₕ↓ iS = shape-conds (≤-trans lteS (hcond iS)) lteE

shapeₜ↓ : ∀ {i h t} → is-shape i h (1+ t) → is-shape i h t
shapeₜ↓ iS = shape-conds (hcond iS) (≤-trans lteS (tcond iS))

full-shape : ∀ i → is-shape (1+ i) i (hom-size (1+ i) i)
full-shape i = shape-conds lteS lteE

-- Equivalence relation on shapes

infix 90 _~[_]_ _~⋆⟨_⟩[_]_

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

-- Shape restriction

#-factors-of_through_from :
  ∀ {i h m} (g : hom i h) (f : hom i m) (α : hom m h)
  → Σ[ k ∶ ℕ ] to-ℕ (idx-of α) + k ≤ hom-size m h
#-factors-of_through_from {h = h} {m} g f α =
  #-hom[ m , h ]-from (λ α → α ◦ f == g) (λ α → α ◦ f ≟-hom g) α

{-
[_,_,_]·ₛ : (i h t : ℕ) {m : ℕ} (f : hom i m) → ℕ × ℕ × ℕ
[_,_,_]·ₛ i h (1+ O) {m} f =
  if h <? m ∶
    (λ h<m →
      if O <? hom-size m h ∶
        (λ O<hom-size → (m , h , k O<hom-size))
      else λ _ → (m , h , O))
  else λ _ → (m , m , O)
  where
  module _ (O<hom-size : O < hom-size m h) where
    [O]ₘₕ : hom m h
    [O]ₘₕ = hom[ m , h ]# (O , O<hom-size)

    O<hom-size-ih : O < hom-size i h
    O<hom-size-ih = ≤-<-< (O≤ _) (idx<hom-size ([O]ₘₕ ◦ f))

    #-factors = #-factors-of (hom[ i , h ]# (O , O<hom-size-ih))
                  through f from [O]ₘₕ
    k = fst #-factors
[_,_,_]·ₛ i h (2+ t) {m} f = {!!}
[ i , 1+ h , O ]·ₛ f = [ i , h , hom-size i h ]·ₛ f
[_,_,_]·ₛ i O O {m} f = (m , O , O)
-}

{- Sieves -}

record LinearSieve (i : ℕ) : Type ℓₘ where
  constructor S[_,_]
  field
    height width : ℕ
    ⦃ shape-cond ⦄ : is-shape i height width
    char : DSM i
    char-∋-cond :
      ∀ {m} (f : hom i m)
      → (char ∋ f) == to-Bool (is-(i , height , width)-admissible? f)

open LinearSieve

-- data <ₛᵥ : Type ℓₘ where

linear-sieve : (i h t : ℕ) → is-shape i h t → LinearSieve i
linear-sieve i h t iS =
  S[ h , t ] ⦃ iS ⦄
    (λ _ f → to-Bool (is-(i , h , t )-admissible? f))
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
