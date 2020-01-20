{-# OPTIONS --exact-split --safe --prop #-}
module Data.Bool.Definition where

open import Universes

data Bool : 𝒰₀ ˙ where
  true false : Bool

_and_ : (b₀ b₁ : Bool) → Bool
true and b₁ = b₁
false and _ = false

_or_ : (b₀ b₁ : Bool) → Bool
true or _ = true
false or b₁ = b₁

not : (b : Bool) → Bool
not true = false
not false = true
