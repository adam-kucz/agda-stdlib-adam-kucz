{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Proposition.Unit where

open import PropUniverses

data ⊤ : 𝒰₀ ᵖ where
  instance ⋆ₚ : ⊤

open ⊤ public
