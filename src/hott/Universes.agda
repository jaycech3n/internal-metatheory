{-# OPTIONS --without-K --rewriting #-}

{- Agda notation for type universes à la Escardo -}

module hott.Universes where

open import hott.Base public

_⁺ = lsuc

_̇  : (ℓ : ULevel) → Type (ℓ ⁺)
𝒰 ̇  = Type 𝒰

Universe = ULevel

-- We don't have Setω by default.
module UniversePolymorphism where
  open import Agda.Primitive using () renaming (Setω to Typeω) public
  𝒰ω = Typeω
