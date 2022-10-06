{-# OPTIONS --without-K #-}

module hott.Base where

open import HoTT
  renaming
  ( lsucc     to lsuc
  ; lmax      to _l⊔_
  ; transport to transp
  ; [_]       to ∣_∣ )
  public
