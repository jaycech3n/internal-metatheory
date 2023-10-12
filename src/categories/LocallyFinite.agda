{-# OPTIONS --without-K --rewriting #-}

module categories.LocallyFinite where

open import categories.Semicategories public

-- Untruncatedly finite hom sets
record LocallyFiniteWildSemicategoryStructure {ℓₒ ℓₘ} {Ob : Type ℓₒ}
  (C : WildSemicategoryStructure ℓₒ ℓₘ Ob)
  : Type (lsuc (ℓₒ ∪ ℓₘ)) where
  open WildSemicategoryStructure C

  field
    hom-finite : ∀ x y → Σ[ n ː ℕ ] (hom x y ≃ Fin n)

  private
    module basic-definitions where
      abstract
        hom-size : (x y : Ob) → ℕ
        hom-size x y = fst (hom-finite x y)

        hom-equiv : (x y : Ob) → hom x y ≃ Fin (hom-size x y)
        hom-equiv x y = snd (hom-finite x y)

        idx-of : ∀ {x y} → hom x y → Fin (hom-size x y)
        idx-of {x} {y} f = –> (hom-equiv x y) f

        hom[_,_]# : ∀ x y → Fin (hom-size x y) → hom x y
        hom[ x , y ]# i = <– (hom-equiv x y) i

        hom#-idx : ∀ {x y} (f : hom x y)
                   → hom[ x , y ]# (idx-of f) == f
        hom#-idx {x} {y} f = <–-inv-l (hom-equiv x y) f

        idx-hom# : ∀ {x y} (i : Fin (hom-size x y))
                   → idx-of (hom[ x , y ]# i) == i
        idx-hom# {x} {y} i = <–-inv-r (hom-equiv x y) i

        idx<hom-size : ∀ {x y} (f : hom x y) → to-ℕ (idx-of f) < hom-size x y
        idx<hom-size f = snd (idx-of f)

      _≺_ : ∀ {x y} (f g : hom x y) → Type₀
      f ≺ g = idx-of f <-Fin idx-of g

      _≼_ : ∀ {x y} (f g : hom x y) → Type₀
      f ≼ g = idx-of f ≤-Fin idx-of g

      #[_] : (t : ℕ) (x y : Ob) → t < hom-size x y → hom x y
      #[ t ] x y u = hom[ x , y ]#(t , u)

      {- Not sure if the following will end up being useful...
      next : ∀ {x y} → hom x y → hom x y
      next {x} {y} f with hom-size x y | inspect (hom-size x) y | idx-of f
      ... | .(1+ idx) | _ | idx , ltS = f
      ... | 1+ n | have p | idx , ltSR idx<n =
        hom[ x , y ]# (1+ idx , transp! (_ <_) p (<-ap-S idx<n))
      -}

  open basic-definitions public

  private
    module hom-equality where
      hom=' : ∀ {x y} {f g : hom x y}
        → idx-of f == idx-of g
        → f == g
      hom=' {x} {y} {f = f} {g = g} p =
        f =⟨ ! (hom#-idx f) ⟩
        hom[ x , y ]# (idx-of f) =⟨ ap hom[ x , y ]# p ⟩
        hom[ x , y ]# (idx-of g) =⟨ hom#-idx g ⟩
        g =∎

      hom= : ∀ {x y} {f g : hom x y}
        → to-ℕ (idx-of f) == to-ℕ (idx-of g)
        → f == g
      hom= = hom=' ∘ Fin=

      #[]-eq : ∀ t x y u u' → #[ t ] x y u == #[ t ] x y u'
      #[]-eq t x y u u' = ap hom[ x , y ]# (Fin= idp)

  open hom-equality public

  private
    module decidability where
      _≟-hom_ : ∀ {x y} → has-dec-eq (hom x y)
      f ≟-hom g = if (idx-of f ≟-Fin idx-of g)
                    (λ  p → inl (hom=' p))
                    (λ ¬p → inr (¬p ∘ ap idx-of))

      Σ-hom? : ∀ {ℓ} {x y} (P : hom x y → Type ℓ)
               → ((f : hom x y) → Dec (P f))
               → Dec (Σ[ f ː hom x y ] (P f))
      Σ-hom? {ℓ} {x} {y} P u =
        transp (Dec ∘ Σ (hom x y)) (λ= (ap P ∘ <–-inv-l e)) dec-hom
          where
          n = hom-size x y
          e = hom-equiv x y

          u' : (i : Fin n) → Dec (P (<– e i))
          u' = bwd-transp-Π-dom e u

          dec-Fin : Dec (Σ[ i ː Fin n ] P (<– e i))
          dec-Fin = Σ-Fin? (P ∘ (<– e)) u'

          dec-hom : Dec (Σ[ f ː hom x y ] P (<– e (–> e f)))
          dec-hom = if dec-Fin
                      (λ  u → inl (fwd-transp-Σ-dom e u))
                      (λ ¬u → inr (λ (f , p) → ¬u (–> e f , p)))

      _≺?_ : ∀ {x y} → Decidable $ _≺_ {x} {y}
      f ≺? g = (idx-of f) <?-Fin (idx-of g)

      _≼?_ : ∀ {x y} → Decidable $ _≼_ {x} {y}
      f ≼? g = (idx-of f) ≤?-Fin (idx-of g)

  open decidability

  private
    module hom-order {x y : Ob} where
      ≺-trans : {f g h : hom x y} → f ≺ g → g ≺ h → f ≺ h
      ≺-trans = <-trans

      ≼-trans : {f g h : hom x y} → f ≼ g → g ≼ h → f ≼ h
      ≼-trans {f} {g} {h} u v =
        ≤-Fin-trans {hom-size x y} {idx-of f} {idx-of g} {idx-of h} u v

      ≼-≺-≺ : {f g h : hom x y} → f ≼ g → g ≺ h → f ≺ h
      ≼-≺-≺ = ≤-<-<

      ≺S-≼ : (f : hom x y) (t : ℕ)
        {u : 1+ t < hom-size x y} {v : t < hom-size x y}
        → f ≺ #[ 1+ t ] x y u → f ≼ #[ t ] x y v
      ≺S-≼ f t {u} {v} w = transp (_ ≤_) (ap to-ℕ $ ! $ idx-hom# _) w'
        where
        w' : idx-of f ≤-Fin (t , v)
        w' = <S-≤ $ transp (_ <_) (ap to-ℕ $ idx-hom# _) w

      idx≤-≼ : (f g : hom x y) → idx-of f ≤-Fin idx-of g → f ≼ g
      idx≤-≼ f g u = u

      abstract
        =-≼ : {f g : hom x y} → f == g → f ≼ g
        =-≼ idp = inl idp

        ¬≺-self : (f : hom x y) → ¬ (f ≺ f)
        ¬≺-self f = ¬<-self

        ≺-trichotomy : (f g : hom x y) → (f == g) ⊔ (f ≺ g) ⊔ (g ≺ f)
        ≺-trichotomy f g = ⊔-rec
          (inl ∘ hom=')
          (λ{ (inl u) → inr $ inl u
            ; (inr u) → inr $ inr u })
          $ Fin-trichotomy (idx-of f) (idx-of g)

        ≺-dichot : (f g : hom x y) → (f ≺ g) ⊔ (g ≼ f)
        ≺-dichot f g = ⊔-rec
          (λ{ idp → inr (=-≼ idp) })
          (λ{ (inl u) → inl u ; (inr u) → inr (inr u) })
          $ ≺-trichotomy f g

        ≺-contrapos : (f' g' f g : hom x y) → (g ≼ f → g' ≼ f') → f' ≺ g' → f ≺ g
        ≺-contrapos f' g' f g w f'≺g' = ⊔-rec
          (idf _)
          (λ g≼f → ⊥-rec $ ¬≺-self _ $ ≼-≺-≺ (w g≼f) f'≺g')
          $ ≺-dichot f g

      module _ (u : O < hom-size x y) where
        [O]-min : (f : hom x y) → #[ O ] x y u ≼ f
        [O]-min f = transp (_≤-Fin (idx-of f)) (! $ idx-hom#(O , u)) (O≤ _)

        ≼[O] : (f : hom x y) → f ≼ #[ O ] x y u → f == #[ O ] x y u
        ≼[O] f (inl p) = hom= p
        ≼[O] f (inr v) = ⊥-rec $ ≮O _
          (transp (λ ◻ → to-ℕ (idx-of f) < to-ℕ ◻) (idx-hom# _) v)

  open hom-order public

  private
    module hom-lemmas where
      hom[_,_]-inhab : ∀ x y → hom x y → O < hom-size x y
      hom[ x , y ]-inhab f = ≤-<-< (O≤ _) (idx<hom-size f)

      hom-is-set : ∀ {x y} → is-set (hom x y)
      hom-is-set {x} {y} = equiv-preserves-level e' ⦃ Lift-level Fin-is-set ⦄
                             where
                             n = hom-size x y
                             e = hom-equiv x y
                             e' : Lift {j = ℓₘ} (Fin n) ≃ hom x y
                             e' = (lift-equiv ∘e e)⁻¹

      _divides_ : ∀ {x y z} (f : hom x y) (h : hom x z) → Type ℓₘ
      _divides_ {y = y} {z} f h = Σ[ g ː hom y z ] g ◦ f == h

      _∣_ : ∀ {x y z} (f : hom x y) (h : hom x z) → Dec (f divides h)
      f ∣ h = Σ-hom? (λ g → g ◦ f == h) (λ g → g ◦ f ≟-hom h)

  open hom-lemmas public

  {- Unused for now; was meant to be a more "semantic" way of implementing
  -- cosieve restriction for the internal inverse diagram construction.
  private
    module counting where
      -- The number of (g : hom x y) satisfying f ≼ g and (P g)
      #-hom[_,_]-from_st :
        ∀ {ℓ} x y
        → (f : hom x y)
        → (P : hom x y → Type ℓ)
        → ((f : hom x y) → Dec (P f))
        → ℕ
      #-hom[ x , y ]-from f st P P? =
        #-Fin n from (idx-of f) to n , lteE and idx<hom-size f
          st (P ∘ hom[ x , y ]#) (P? ∘ hom[ x , y ]#)
        where n = hom-size x y

      #-hom-ub :
        ∀ {ℓ} x y (f : hom x y)
          (P : hom x y → Type ℓ) (P? : (f : hom x y) → Dec (P f))
        → #-hom[ x , y ]-from f st P P? ≤ hom-size x y
      #-hom-ub x y f P P? =
        #-Fin-coarse-ub n (idx-of f) n lteE (idx<hom-size f) _ _
        where n = hom-size x y

      -- Counting factors
      #-factors :
        ∀ {i h m} (t : Fin (hom-size i h)) (f : hom i m)
        → O < hom-size m h
        → Σ[ n ː ℕ ] n ≤ hom-size m h
      #-factors{i} {h} {m} t f u =
        #-hom[ m , h ]-from [O] st (λ α → α ◦ f ≼ [t]) (λ α → α ◦ f ≼? [t]) ,
        #-hom-ub m h [O] (λ α → α ◦ f ≼ [t]) (λ α → α ◦ f ≼? [t])
        where
          [O] = hom[ m , h ]# (O , u)
          [t] = hom[ i , h ]# t

      #-factors-of-hom[_,_]≤[_]-through :
        ∀ i h {m} (t : Fin (hom-size i h)) (f : hom i m)
        → O < hom-size m h
        → ℕ
      #-factors-of-hom[_,_]≤[_]-through i h {m} t f u =
        fst (#-factors {i} {h} {m} t f u)

      #-factors-ub :
        ∀ {i h m} t (f : hom i m) (u : O < hom-size m h)
        → #-factors-of-hom[ i , h ]≤[ t ]-through f u ≤ hom-size m h
      #-factors-ub t f u = snd (#-factors t f u)
  -}
