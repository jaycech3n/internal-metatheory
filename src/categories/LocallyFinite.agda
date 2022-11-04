{-# OPTIONS --without-K #-}

module categories.LocallyFinite where

open import categories.Semicategories public

-- Untruncatedly finite hom sets
record LocallyFinitelyIndexedWildSemicategoryStructure {ℓₒ ℓₘ} {Ob : Type ℓₒ}
  (C : WildSemicategoryStructure ℓₒ ℓₘ Ob)
  : Type (lsuc (ℓₒ l⊔ ℓₘ)) where
  open WildSemicategoryStructure C

  field
    hom-finitely-indexed : ∀ x y → Σ[ n ∶ ℕ ] (hom x y ≃ Fin n)

  private
    module basic-definitions where
      abstract
        hom-size : (x y : Ob) → ℕ
        hom-size x y = fst (hom-finitely-indexed x y)

        hom-equiv : (x y : Ob) → hom x y ≃ Fin (hom-size x y)
        hom-equiv x y = snd (hom-finitely-indexed x y)

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

      module _ {x y : Ob} where
        _≺_ : (f g : hom x y) → Type₀
        f ≺ g = idx-of f <-Fin idx-of g

        _≼_ : (f g : hom x y) → Type₀
        f ≼ g = idx-of f ≤-Fin idx-of g

        _≺?_ : Decidable _≺_
        f ≺? g = (idx-of f) <?-Fin (idx-of g)

        _≼?_ : Decidable _≼_
        f ≼? g = (idx-of f) ≤?-Fin (idx-of g)

  open basic-definitions public

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

      hom= : ∀ {x y} {f g : hom x y}
             → idx-of f == idx-of g
             → f == g
      hom= {x} {y} {f = f} {g = g} p =
        f =⟨ ! (hom#-idx f) ⟩
        hom[ x , y ]# (idx-of f) =⟨ ap hom[ x , y ]# p ⟩
        hom[ x , y ]# (idx-of g) =⟨ hom#-idx g ⟩
        g =∎

      _≟-hom_ : ∀ {x y} → has-dec-eq (hom x y)
      f ≟-hom g = if (idx-of f ≟-Fin idx-of g)
                     (λ  p → inl (hom= p))
                     (λ ¬p → inr (¬p ∘ ap idx-of))

      Σ-hom? : ∀ {ℓ} {x y} (P : hom x y → Type ℓ)
               → ((f : hom x y) → Dec (P f))
               → Dec (Σ[ f ∶ hom x y ] (P f))
      Σ-hom? {ℓ} {x} {y} P u =
        transp (Dec ∘ Σ (hom x y)) (λ= (ap P ∘ <–-inv-l e)) dec-hom
          where
          n = hom-size x y
          e = hom-equiv x y

          u' : (i : Fin n) → Dec (P (<– e i))
          u' = bwd-transp-Π-dom e u --tr-Π-≃-r (Dec ∘ P) e u

          dec-Fin : Dec (Σ[ i ∶ Fin n ] P (<– e i))
          dec-Fin = Σ-Fin? (P ∘ (<– e)) u'

          dec-hom : Dec (Σ[ f ∶ hom x y ] P (<– e (–> e f)))
          dec-hom = if dec-Fin
                       (λ  u → inl (fwd-transp-Σ-dom e u))
                       (λ ¬u → inr (λ (f , p) → ¬u (–> e f , p)))

      -- The number of (g : hom x y) satisfying f ≼ g and (P g)
      #-hom[_,_]-from : ∀ {ℓ} x y
                        → (P : hom x y → Type ℓ)
                        → ((f : hom x y) → Dec (P f))
                        → (f : hom x y)
                        → Σ[ k ∶ ℕ ] to-ℕ (idx-of f) + k ≤ hom-size x y
      #-hom[ x , y ]-from P dec f =
        #-Fin-from {n = hom-size x y} (P ∘ hom[ x , y ]#) (dec ∘ hom[ x , y ]#)
          (idx-of f) {hom-size x y ∸ to-ℕ (idx-of f) ∸ 1} {β∸1 (∸-nonzero (idx<hom-size f))}

      _factors-through_ : ∀ {x y z} (h : hom x z) (f : hom x y) → Type ℓₘ
      _factors-through_ {y = y} {z} h f = Σ[ g ∶ hom y z ] g ◦ f == h

      _factors-through?_ : ∀ {x y z} (h : hom x z) (f : hom x y)
                           → Dec (h factors-through f)
      h factors-through? f = Σ-hom? (λ g → (g ◦ f) == h) (λ g → g ◦ f ≟-hom h)

  open hom-lemmas public
