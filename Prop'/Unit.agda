{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Prop'.Unit where

open import PropUniverses

data ⊤ : 𝒰₀ ᵖ where
  instance ⋆ₚ : ⊤

open ⊤ public
