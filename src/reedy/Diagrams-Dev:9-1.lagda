\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=4 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Dev:9-1 {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I

import reedy.CosieveShapes as Sh
import reedy.ShapeOrder as Ord
open Sh I
open Ord I

open import reedy.ShapeCountFactors I
open ShapeCountFactors-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr

\end{code}


Declarations
------------

Mutually define the filler context
  𝔻< i ≡ A₀ : 𝔸₀, ..., Aᵢ₋₁ : 𝔸ᵢ₋₁,
the type Match of the matching functor, and
the actual matching functor MF.

\begin{code}

𝔻< : (b : ℕ) → Con
record Match (b : ℕ) (bsh₀ : [ b ]BoundedShape) : Type (ℓₒ ∪ ℓₘ ∪ ℓₘᴵ)
MF< : (b : ℕ) (bsh₀ : [ b ]BoundedShape) → Match b bsh₀

\end{code}


Definitions
-----------

𝔻< and Match can be defined immediately.

\begin{code}

record Match b bsh₀ where
  eta-equality
  field
    Mᵒ : (bsh : [ b ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< b)

  M : (bsh : [ b ]BoundedShape) → bsh ≤ₛᵇ bsh₀ → Con
  M bsh w = close $ Mᵒ bsh w

  field
    M⃗ :
      (bsh@(shape i h t s , u) : [ b ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)

𝔻< O = ◆
𝔻< (1+ O) = ◆ ∷ U
𝔻< (2+ b) = 𝔻< (1+ b) ∷ Πₜₑₗ (Match.Mᵒ (MF< (1+ b) tot) tot (inl idp)) U
  where tot = total-shape-1+ b , ltS

\end{code}


Definition of MF<
-----------------

We define (MF< b) for b = 1 and b = 2+ b' separately.

In each case, the definition of (MF< b bsh₀) is by well founded induction on the
order <ₛᵇ on b-bounded shapes. Concretely, this means we construct (MF< b bsh₀)
assuming
  MF<-ind : ∀ bsh → bsh < bsh₀ → Match b bsh.

For each b, we further distinguish cases for
  bsh₀ ∈ {
    (0, 0, 0),
    (1+ i₀, 0, 0),
    (i₀, 1+ h₀, 0),
    (i₀, h₀, 1+ t₀)
    }
so that we can refer to the immediate predecessor of bsh₀.

\begin{code}

module MF<1 where

  \end{code}

  In the base case bsh₀ = (0, 0, 0), everything is trivial.

  \begin{code}

  module case[0,0,0] s₀ where

    bsh₀ = shape O O O s₀ , ltS

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< 1)
    Mᵒ bsh w = •

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w

    M⃗ :
      (bsh@(shape i h t s , u) : [ 1 ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)
    M⃗ bsh (inl idp) {j} f rs rw = ⊥-rec (≮O j (hom-inverse _ _ f))
    M⃗ bsh (inr (on-𝑖 ())) f rs rw
    M⃗ bsh (inr (on-ℎ ())) f rs rw
    M⃗ bsh (inr (on-𝑡 ())) f rs rw


  module case[1+i₀,0,0] i₀ s₀
    (ind :
      (bsh : [ 1 ]BoundedShape)
      → bsh <ₛᵇ shape (1+ i₀) O O s₀ , ltS
      → Match 1 bsh)
    where

    bsh₀ = shape (1+ i₀) O O s₀ , ltS
    pbsh₀ = full-bshape i₀ O ltS

    -- The matching functor up to the previous 1-bounded shape
    MF[i₀,0,full] = ind pbsh₀ (on-𝑖 ltS)
    -- and its components
    Mᵒ[i₀,0,full] = Match.Mᵒ MF[i₀,0,full]
    M⃗[i₀,0,full] = Match.M⃗ MF[i₀,0,full]

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< 1)
    Mᵒ bsh (inl idp) = •

    -- For bsh < bsh₀, take definitions from MF at the predecessor of bsh₀.
    -- We'd think to just immediately define:
    --   Mᵒ bsh@(sh , u) (inr w) = Mᵒ[i₀,0,full] bsh bsh≤pbsh₀
    --     where bsh≤pbsh₀ = bdd-<ₛS𝑖00-≤ₛ𝑖bfull sh u w
    -- !! But then, the type of M⃗ would require a proof of a particular equality
    -- !! to be maintained *across* the induction: specifically, we'd need to
    -- !! know something like
    -- !!   Match.Mᵒ (ind bsh _) (j, 0, 0) == •
    -- !! for bsh < bsh₀ and (j, 0, 0) ≤ bsh.
    -- !! Thus we instead split into cases on bsh, and *define* Mᵒ to be • in
    -- !! the case that we need.
    -- Summary: in order to have convenient definitional equalities when
    -- defining M⃗, we first split into cases on bsh.
    Mᵒ (shape i O O s , u) (inr w) = • -- want this definitionally
    Mᵒ bsh@(shape i O (1+ t) s , u) (inr w) =
      Mᵒ[i₀,0,full] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = bdd-<ₛS𝑖00-≤ₛ𝑖bfull (fst bsh) u w
    Mᵒ (shape i (1+ h) t s , ltSR ()) (inr w)

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w

    M⃗ :
      (bsh@(shape i h t s , u) : [ 1 ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)

    M⃗ bsh (inl idp) f .s₀ (inl idp) = ⊥-rec (¬<-self (hom-inverse _ _ f))
    M⃗ bsh (inl idp) {j} f rs (inr rw) = id

    M⃗ bsh (inr w) f rs (inl p) = {!-- impossible; bsh < bsh₀, f : i → j and j == i₀!}
    M⃗ bsh@(shape i .O O s , ltS) (inr w) f rs (inr rw) = id
    -- The case splitting on bsh in the definition of (Mᵒ bsh (inr w)) above
    -- means we have to case-analyze (count-factors i 0 (1+ t) s f) in the type
    -- below.
    M⃗ bsh@(shape i .O (1+ t) s , ltS) (inr w) f rs (inr rw) = {!!}


  module case[i₀,0,1+t₀] i₀ t₀ s₀
    (ind :
      (bsh : [ 1 ]BoundedShape)
      → bsh <ₛᵇ shape i₀ O (1+ t₀) s₀ , ltS
      → Match 1 bsh)
    where

    bsh₀ = shape i₀ O (1+ t₀) s₀ , ltS
    pbsh₀ = prev-bshape s₀ ltS -- ≡ shape i₀ O t₀ (prev-is-shape s₀) , ltS

    -- The matching functor up to the previous 1-bounded shape
    MF[i₀,0,t₀] = ind pbsh₀ (on-𝑡 ltS)
    -- and its components
    Mᵒ[i₀,0,t₀] = Match.Mᵒ MF[i₀,0,t₀]
    M⃗[i₀,0,t₀] = Match.M⃗ MF[i₀,0,t₀]

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< 1)
    -- Copy previous definition if bsh < bsh₀
    Mᵒ bsh (inr w) = Mᵒ[i₀,0,t₀] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = <ₛS𝑡-≤ₛ𝑡 (fst bsh) w
    -- Otherwise, define:
    Mᵒ (shape .i₀ .O .(1+ t₀) .s₀ , ltS) (inl idp) = pMᵒ ‣ A₀ [ πₜₑₗ pMᵒ ]
      where
      pMᵒ = Mᵒ[i₀,0,t₀] pbsh₀ (inl idp)
      A₀ : Ty (𝔻< 1)
      A₀ = generic-closed-type-in ◆

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w

    \end{code}

    When we define (M⃗ (i₀, O, 1+t₀) f), we require its type to compute to the
    appropriate value, depending on whether or not f divides [t]ⁱₕ. To actually
    allow this computation to occur, this type needs to expose the discriminant as
    an extra argument of type (Dec (f ∣ #[ t₀ ] i₀ 0 _)).

    \begin{code}

    M⃗[i₀,0,1+t₀]-deptype :
      {j : ℕ} (f : hom i₀ j)
      → let v₀ = <-from-is-shape s₀ in
        (d : Dec (f ∣ #[ t₀ ] i₀ O v₀))
      → let r = count-factors-aux i₀ O t₀ v₀ f d in
        (rs : is-shape j O r)
      → let rsh = shape j O r rs , ltS in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Type _
    M⃗[i₀,0,1+t₀]-deptype {j} f d rs rw =
      Sub (M (shape i₀ O (1+ t₀) s₀ , ltS) (inl idp))
          (M (shape j O r rs , ltS) rw)
      where v₀ = <-from-is-shape s₀
            r = count-factors-aux i₀ O t₀ v₀ f d

    \end{code}

    We expose the discriminant in an auxiliary implementation of M⃗ (i, h, t+1); this
    will be needed when defining M⃗◦.

    \begin{code}

    M⃗[i₀,0,1+t₀] :
      {j : ℕ} (f : hom i₀ j)
      → let v₀ = <-from-is-shape s₀ in
        (d : Dec (f ∣ #[ t₀ ] i₀ O v₀))
      → let r = count-factors-aux i₀ O t₀ v₀ f d in
        (rs : is-shape j O r)
      → let rsh = shape j O r rs , ltS in
        (rw : rsh ≤ₛᵇ bsh₀)
      → M⃗[i₀,0,1+t₀]-deptype f d rs rw
    M⃗[i₀,0,1+t₀] f (inl yes) rs rw = {!!}
    M⃗[i₀,0,1+t₀] f (inr no) rs (inl p) = {!-- impossible!}
    M⃗[i₀,0,1+t₀] f (inr no) rs (inr rw) =
      M⃗[i₀,0,t₀] pbsh₀ (inl idp) f rs rsh≤pbsh₀ ◦ˢᵘᵇ π _
      where rsh≤pbsh₀ = <ₛS𝑡-≤ₛ𝑡 (rstrₛ (fst pbsh₀) f rs) rw

    \end{code}

    \begin{code}

    M⃗ :
      (bsh@(shape i h t s , u) : [ 1 ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)

    M⃗ bsh (inr w) f rs (inl p) = {!p!}

    M⃗ bsh (inr w) f rs (inr rw) =
      M⃗[i₀,0,t₀] bsh bsh≤pbsh₀ f rs rsh≤pbsh₀
      where
      bsh≤pbsh₀ = <ₛS𝑡-≤ₛ𝑡 (fst bsh) w

      -- Need the exact definition of rsh≤pbsh₀ below, otherwise this clause's
      -- definition does not typecheck!
      -- e.g. this alternative definition doesn't work:
      -- ≤ₛ-trans (rstrₛ-≤ₛ (fst bsh) f) (<ₛS𝑡-≤ₛ𝑡 (fst bsh) w)
      rsh≤pbsh₀ = <ₛS𝑡-≤ₛ𝑡 (rstrₛ (fst bsh) f rs) rw

    M⃗ (shape .i₀ .O .(1+ t₀) .s₀ , ltS) (inl idp) {j} f rs rw =
      M⃗[i₀,0,1+t₀] f (discrim i₀ O t₀ (<-from-is-shape s₀) f) rs rw

    \end{code}

\begin{code}

module MF<2+ (b : ℕ) where

  module case[0,0,0] s₀ u₀ where

    bsh₀ : [ 2+ b ]BoundedShape
    bsh₀ = shape O O O s₀ , u₀

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< (2+ b))
    Mᵒ bsh w = •

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w

    M⃗ :
      (bsh@(shape i h t s , u) : [ 2+ b ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)
    M⃗ bsh (inl idp) {j} f rs rw = ⊥-rec (≮O j (hom-inverse _ _ f))
    M⃗ bsh (inr (on-𝑖 ())) f rs rw
    M⃗ bsh (inr (on-ℎ ())) f rs rw
    M⃗ bsh (inr (on-𝑡 ())) f rs rw

  module case[1+i₀,0,0] i₀ s₀ u₀
    (ind :
      (bsh : [ 2+ b ]BoundedShape)
      → bsh <ₛᵇ shape (1+ i₀) O O s₀ , u₀
      → Match (2+ b) bsh)
    where

    bsh₀ : [ 2+ b ]BoundedShape
    bsh₀ = shape (1+ i₀) O O s₀ , u₀

    pbsh₀ = full-bshape i₀ (1+ b) ltS

    MF[i₀,1+b,full] = ind pbsh₀ (on-𝑖 ltS)
    Mᵒ[i₀,1+b,full] = Match.Mᵒ MF[i₀,1+b,full]
    M⃗[i₀,1+b,full] = Match.M⃗ MF[i₀,1+b,full]

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< (2+ b))
    Mᵒ bsh (inl p) = •
    Mᵒ bsh@(shape i O O s , u) (inr w) = • -- want this definitionally
    Mᵒ bsh@(shape i O (1+ t) s , u) (inr w) =
      Mᵒ[i₀,1+b,full] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = bdd-<ₛS𝑖00-≤ₛ𝑖bfull (fst bsh) u w
    Mᵒ bsh@(shape i (1+ h) t s , u) (inr w) =
      Mᵒ[i₀,1+b,full] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = bdd-<ₛS𝑖00-≤ₛ𝑖bfull (fst bsh) u w

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w

    M⃗ :
      (bsh@(shape i h t s , u) : [ 2+ b ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)

    M⃗ bsh (inl idp) {j} f rs (inl q) =
      ⊥-rec $ ¬<-self $ hom-inverse _ _ f ◂$ transp (_< 1+ i₀) q'
      where
      q' : j == 1+ i₀
      q' = shape=-𝑖= q
    M⃗ bsh (inl idp) f rs (inr rw) = id

    M⃗ bsh (inr w) f rs rw = {!!}

  module case[i₀,1+h₀,0] i₀ h₀ s₀ u₀
    (ind :
      (bsh : [ 2+ b ]BoundedShape)
      → bsh <ₛᵇ shape i₀ (1+ h₀) O s₀ , u₀
      → Match (2+ b) bsh)
    where

    bsh₀ : [ 2+ b ]BoundedShape
    bsh₀ = shape i₀ (1+ h₀) O s₀ , u₀

    pbsh₀ = full-bshape i₀ h₀ (S<-< u₀)

    MF[i₀,h₀,full] = ind pbsh₀ (on-ℎ ltS)
    Mᵒ[i₀,h₀,full] = Match.Mᵒ MF[i₀,h₀,full]
    M⃗[i₀,h₀,full] = Match.M⃗ MF[i₀,h₀,full]

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< (2+ b))
    Mᵒ bsh (inl p) = Mᵒ[i₀,h₀,full] pbsh₀ (inl idp)
    -- Similarly to the (1+ i₀, 0, 0) case, we further split on bsh in the case
    -- bsh < bsh₀ in order to obtain definitional equalities and avoid the
    -- thorny problem of having to define coherences across the well founded
    -- induction.
    Mᵒ bsh@(shape i (1+ h) O s , u) (inr w) =
      Mᵒ[i₀,h₀,full] pbsh pbsh≤pbsh₀ -- want this definitionally
      where
      pbsh = full-bshape i h (S<-< u)
      bsh≤pbsh₀ = <ₛSℎ0-≤ₛℎfull (fst bsh) w
      pbsh≤pbsh₀ = ≤ₛ-trans (inr (on-ℎ ltS)) bsh≤pbsh₀
    Mᵒ bsh@(shape i (1+ h) (1+ t) s , u) (inr w) =
      Mᵒ[i₀,h₀,full] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = <ₛSℎ0-≤ₛℎfull (fst bsh) w
    Mᵒ bsh@(shape i O t s , u) (inr w) =
      Mᵒ[i₀,h₀,full] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = <ₛSℎ0-≤ₛℎfull (fst bsh) w

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w

    M⃗ :
      (bsh@(shape i h t s , u) : [ 2+ b ]BoundedShape)
      (w : bsh ≤ₛᵇ bsh₀)
      {j : ℕ} (f : hom i j)
      → let r = count-factors i h t s f in
        (rs : is-shape j h r)
      → let rsh = shape j h r rs , u in
        (rw : rsh ≤ₛᵇ bsh₀)
      → Sub (M bsh w) (M rsh rw)

    M⃗ bsh (inl idp) {j} f rs (inl q) =
      ⊥-rec $ ¬<-self $ hom-inverse _ _ f ◂$ transp (_< i₀) q'
      where
      q' : j == i₀
      q' = shape=-𝑖= q
    M⃗ bsh (inl idp) f rs (inr rw) =
      idd {!!} ◦ˢᵘᵇ M⃗[i₀,h₀,full] pbsh₀ (inl idp) f rs' rstr≤pbsh₀
      where
      rs' = count-factors-is-shape i₀ h₀ (hom-size i₀ h₀) _ f
      rstr≤pbsh₀ = rstrₛ-≤ₛ (fst pbsh₀) f
    M⃗ bsh (inr w) f rs (inl p) = {!-- impossible!}
    M⃗ bsh (inr w) f rs (inr rw) = {!!}


  module case[i₀,h₀,1+t₀] i₀ h₀ t₀ s₀ u₀
    (ind :
      (bsh : [ 2+ b ]BoundedShape)
      → bsh <ₛᵇ shape i₀ h₀ (1+ t₀) s₀ , u₀
      → Match (2+ b) bsh)
    where

    bsh₀ : [ 2+ b ]BoundedShape
    bsh₀ = shape i₀ h₀ (1+ t₀) s₀ , u₀

    pbsh₀ = prev-bshape s₀ u₀

    MF[i₀,h₀,t₀] = ind pbsh₀ (on-𝑡 ltS)
    Mᵒ[i₀,h₀,t₀] = Match.Mᵒ MF[i₀,h₀,t₀]
    M⃗[i₀,h₀,t₀] = Match.M⃗ MF[i₀,h₀,t₀]

    Mᵒ : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Tel (𝔻< (2+ b))
    Mᵒ bsh (inr w) = Mᵒ[i₀,h₀,t₀] bsh bsh≤pbsh₀
      where bsh≤pbsh₀ = <ₛS𝑡-≤ₛ𝑡 (fst bsh) w

    Mᵒ (shape .i₀ h₀ .(1+ t₀) .s₀ , u) (inl idp) =
      pMᵒ ‣ {!!}
      where
      pMᵒ : Tel (𝔻< (2+ b))
      pMᵒ = Mᵒ[i₀,h₀,t₀] pbsh₀ (inl idp)

      -- Need to use "Aₕ₀ : 𝔸ₕ₀";
      -- but what are their types, which indices exactly?
      -- 𝔸ₕ₀ : Ty (𝔻)

    M : ∀ bsh → bsh ≤ₛᵇ bsh₀ → Con
    M bsh w = close $ Mᵒ bsh w


\end{code}


Put everything together:
------------------------

\begin{code}

MF<[1+_]-inddef :
  ∀ b (bsh₀ : [ 1+ b ]BoundedShape)
  → ((bsh : [ 1+ b ]BoundedShape) → bsh <ₛᵇ bsh₀ → Match (1+ b) bsh)
  → Match (1+ b) bsh₀

MF<[1+ O ]-inddef (shape O O O s₀ , ltS) ind =
  record { Mᵒ = Mᵒ ; M⃗ = M⃗ }
  where open MF<1.case[0,0,0] s₀
MF<[1+ O ]-inddef (shape (1+ i₀) O O s₀ , ltS) ind =
  record { Mᵒ = Mᵒ ; M⃗ = M⃗ }
  where open MF<1.case[1+i₀,0,0] i₀ s₀ ind
MF<[1+ O ]-inddef (shape i₀ .O (1+ t₀) s₀ , ltS) ind =
  record { Mᵒ = Mᵒ ; M⃗ = M⃗ }
  where open MF<1.case[i₀,0,1+t₀] i₀ t₀ s₀ ind
-- MF<[1+ O ]-inddef (shape i₀ (1+ h₀) O s , ltSR ()) ind is impossible

MF<[1+ 1+ b ]-inddef (shape O O O s₀ , u₀) ind =
  record { Mᵒ = Mᵒ ; M⃗ = M⃗ } where
    open MF<2+ b
    open case[0,0,0] s₀ u₀
MF<[1+ 1+ b ]-inddef (shape (1+ i₀) O O s₀ , u₀) ind = {!!}
MF<[1+ 1+ b ]-inddef (shape i₀ (1+ h₀) O s₀ , u₀) ind = {!!}
MF<[1+ 1+ b ]-inddef (shape i₀ h₀ (1+ t₀) s₀ , u₀) ind = {!!}

MF< (1+ b) =
  wf-ind (Match (1+ b)) MF<[1+ b ]-inddef
  where
  open
    WellFoundedInduction [ 1+ b ]BoundedShape _<ₛᵇ_
      (λ bsh₀ → <ₛᵇ-wf {bsh = bsh₀})

\end{code}
