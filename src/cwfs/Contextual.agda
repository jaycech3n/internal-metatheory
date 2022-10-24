{-# OPTIONS --without-K #-}

module cwfs.Contextual where

open import cwfs.CwFs

module _ {ℓₒ ℓₘ ℓᵀʸ ℓᵀᵐ} {C : WildCategory ℓₒ ℓₘ} (cwfstr : CwFStructure ℓᵀʸ ℓᵀᵐ C) where
  open CwFStructure cwfstr
