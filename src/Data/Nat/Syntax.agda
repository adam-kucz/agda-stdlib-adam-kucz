{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Syntax where

open import Data.Nat.Definition

open import PropUniverses
open import Logic using (⊤)
open Logic using (⋆ₚ) public

{-# BUILTIN NATURAL ℕ #-}

record Nat (X : 𝒰 ˙) : 𝒰 ⁺ ˙ where
  field
    Constraint : (n : ℕ) → 𝒰 ᵖ
    fromℕ : (n : ℕ) ⦃ p : Constraint n ⦄ → X

open Nat ⦃ ... ⦄ public using (fromℕ)

{-# BUILTIN FROMNAT fromℕ #-}

instance
  Natℕ : Nat ℕ
  Nat.Constraint Natℕ _ = ⊤
  Nat.fromℕ Natℕ n = n

module Pattern where
  pattern _+1 x = suc x
  pattern _+2 x = suc (suc x)
  pattern _+3 x = suc (suc (suc x))

module Display where
  open Pattern
  {-# DISPLAY _+1 zero = 1 #-}
  {-# DISPLAY _+2 zero = 2 #-}
  {-# DISPLAY _+3 zero = 3 #-}
