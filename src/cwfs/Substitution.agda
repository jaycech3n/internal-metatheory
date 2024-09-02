{-# OPTIONS --without-K --rewriting #-}

-- Substitution in types in a wild cwf should be a (weak) pullback (?)

module cwfs.Substitution where

open import cwfs.CwFs public
open import categories.Pullbacks public

module Substitution-is-pb {ℓₒ} {ℓₘ}
  {C : WildCategory ℓₒ ℓₘ}
  (cwfstruct : CwFStructure C)
  where
