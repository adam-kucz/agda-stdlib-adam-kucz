{-# OPTIONS --without-K --exact-split --safe #-}
module Type.Primitive where

open import Universes

data 𝟘 : 𝒰₀ ˙ where

data 𝟙 : 𝒰₀ ˙ where
  instance ⋆ : 𝟙

open import Type.BinarySum

𝟚 : 𝒰₀ ˙
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆
