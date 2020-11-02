{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Proposition.Exists where

open import PropUniverses

data Exists (X : 𝒰 ˙) : 𝒰 ᵖ where
  an : (x : X) → Exists X

-- better name for creating wrapped objects
example : (x : X) → Exists X
example = an

