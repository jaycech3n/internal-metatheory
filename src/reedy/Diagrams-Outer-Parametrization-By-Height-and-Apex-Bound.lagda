\begin{code}

{-# OPTIONS --without-K --rewriting --termination-depth=10 #-}

open import reedy.SimpleSemicategories
open import cwfs.CwFs
open import cwfs.Pi
open import cwfs.Universe

module reedy.Diagrams-Outer-Parametrization-By-Height-and-Apex-Bound {ℓₘᴵ ℓₒ ℓₘ}
  (I : SimpleSemicategory ℓₘᴵ)
  (I-strictly-oriented : is-strictly-oriented I)
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstr : CwFStructure C)
  (pistr : PiStructure cwfstr)
  (univstr : UniverseStructure cwfstr)
  where

open SimpleSemicategory I
open import reedy.Cosieves I
open Cosieves-StrictlyOriented I-strictly-oriented

open CwFStructure cwfstr renaming (_◦_ to _◦ˢᵘᵇ_ ; ass to assˢᵘᵇ)
open PiStructure pistr
open UniverseStructure univstr
open import cwfs.Telescopes cwfstr
open Πₜₑₗ pistr
open TelIndexedTypes univstr


𝔻[_] : ℕ → Con

Mᵒ[_] :
  (b : ℕ) (i h t : ℕ) (s : shape i h t)
  → b < i → h ≤ b
  → Tel 𝔻[ b ]

M⃗[_] :
  (b : ℕ) (i h t : ℕ) (s : shape i h t)
  (bᵢ : b < i) (bₕ : h ≤ b)
  (j : ℕ) (bⱼ : b < j) (f : hom i j)
  → let cf = count-factors i h t s f in
    (cfs : shape j h cf)
  → Sub (𝔻[ b ] ++ₜₑₗ Mᵒ[ b ] i h t s bᵢ bₕ) (𝔻[ b ] ++ₜₑₗ Mᵒ[ b ] j h cf cfs bⱼ bₕ)

𝔻[ O ] = ◆ ∷ U
𝔻[ 1+ b ] = 𝔻[ b ] ∷ Πₜₑₗ (Mᵒ[ b ] (1+ b) b (hom-size (1+ b) b) (total-shape-1+ b) ltS lteE) U


Mᵒ[ O ] i h O s bᵢ bₕ = •
Mᵒ[ O ] i h (1+ t) s bᵢ bₕ =
  let Mᵒ[O]-prev = Mᵒ[ O ] i h t prev bᵢ bₕ in
  Mᵒ[O]-prev ‣ A₀ [ πₜₑₗ Mᵒ[O]-prev ]
  where
  prev = prev-shape s
  A₀ = generic[ ◆ ]type

Mᵒ[ 1+ b ] i h t s bᵢ bₕ = {!!}


M⃗[ O ] i h t s bᵢ bₕ j bⱼ f cfs = {!!}

M⃗[ 1+ b ] i h t s bᵢ bₕ j bⱼ f cfs = {!!}


{-
Mᵒ[ O ] i .O O s (inl idp) = •
Mᵒ[ O ] i .O (1+ t) s (inl idp) =
  let Mᵒ[O]-prev = Mᵒ[ O ] i O t prev lteE in
  Mᵒ[O]-prev ‣ A₀ [ πₜₑₗ Mᵒ[O]-prev ]
  where
  prev = prev-shape s
  A₀ = generic[ ◆ ]type

Mᵒ[ 1+ b ] i h t s (inr w) = wkₜₑₗ $ Mᵒ[ b ] i h t s (<S-≤ w)
Mᵒ[ 1+ b ] i .(1+ b) O s (inl idp) = wkₜₑₗ $ Mᵒ[ b ] i b (hom-size i b) (full-shape i b) lteE
Mᵒ[ 1+ b ] i .(1+ b) (1+ t) s (inl idp) =
  {!Mᵒ[ 1+ b ] i (1+ b)!}


M⃗[ O ] i .O O s (inl idp) f cfs = id
M⃗[ O ] i .O (1+ t) s (inl idp) f cfs = {!!}

M⃗[ 1+ b ] i h t s (inr w) {j} f cfs =
  let
    Mᵒ[b] = Mᵒ[ b ] i h t s (<S-≤ w)
    Mᵒ∙f = Mᵒ[ b ] j h (count-factors i h t s f) cfs (<S-≤ w)
    Mᵒ[b]tot[1+b] = Mᵒ[ b ] (1+ b) b (hom-size (1+ b) b) (total-shape-1+ b) lteE
    𝔸[1+b] = Πₜₑₗ Mᵒ[b]tot[1+b] U
  in
  wkn-sub Mᵒ[b] Mᵒ∙f (M⃗[ b ] i h t s (<S-≤ w) f cfs) {!!} 𝔸[1+b]
M⃗[ 1+ b ] i h t s (inl idp) f cfs = {!!}
-}

\end{code}
