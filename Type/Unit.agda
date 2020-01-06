{-# OPTIONS --without-K --exact-split --safe #-}
module Type.Unit where

open import Universes

data 𝟙 : 𝒰₀ ˙ where
  instance ⋆ : 𝟙

