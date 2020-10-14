{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Proposition.Wrapped where

open import PropUniverses

data Wrapped (X : 𝒰 ˙) : 𝒰 ᵖ where
  unwrap : (x : X) → Wrapped X

-- better name for creating wrapped objects
wrap : (x : X) → Wrapped X
wrap = unwrap

