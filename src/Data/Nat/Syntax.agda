{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Syntax where

open import Data.Nat.Definition

open import PropUniverses
open import Logic using (⊤)
open Logic using (⋆ₚ) public

{-# BUILTIN NATURAL ℕ #-}

record Nat 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  field
    Constraint : (n : ℕ) → 𝒱 ᵖ
    fromℕ : (n : ℕ) ⦃ p : Constraint n ⦄ → X

open Nat ⦃ ... ⦄ public using (fromℕ)

{-# BUILTIN FROMNAT fromℕ #-}

instance
  Natℕ : Nat 𝒰₀ ℕ
  Nat.Constraint Natℕ _ = ⊤
  Nat.fromℕ Natℕ n = n

module Pattern where
  infixl 130 _+1 _+2 _+3
  pattern _+1 x = suc x
  pattern _+2 x = x +1 +1
  pattern _+3 x = x +2 +1
  pattern one = 0 +1
  pattern two = 0 +2
  pattern three = 0 +3

module Display where
  open Pattern
  {-# DISPLAY _+1 zero = 1 #-}
  {-# DISPLAY _+2 zero = 2 #-}
  {-# DISPLAY _+3 zero = 3 #-}
