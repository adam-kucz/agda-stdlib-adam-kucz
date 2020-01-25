{-# OPTIONS --without-K --exact-split --safe #-}
module Data.ExtendedNat where

open import Universes
open import Data.Nat.Definition

data ℕ∞ : 𝒰₀ ˙ where
  nat : (m : ℕ) → ℕ∞
  ∞ : ℕ∞
