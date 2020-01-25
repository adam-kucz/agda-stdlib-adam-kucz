{-# OPTIONS --without-K --exact-split --safe #-}
module Data.Int.Definition where

open import Universes
open import Data.Nat.Definition

data ℤ : 𝒰₀ ˙ where
  nneg : (n : ℕ) → ℤ
  -[_+1] : (n : ℕ) → ℤ

variable
  x y z : ℤ
