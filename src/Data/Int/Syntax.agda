{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Syntax where

open import Data.Int.Definition

open import PropUniverses
open import Proposition.Unit
open import Proposition.Unit using (⋆ₚ) public
open import Data.Nat.Definition hiding (zero)
open import Data.Nat.Syntax hiding (module Pattern)

record Negative 𝒰 (X : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ⁺ ˙ where
  field
    Constraint : ℕ → 𝒱 ᵖ
    fromNeg : (n : ℕ)⦃ _ : Constraint n ⦄ → X

open Negative ⦃ … ⦄ public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}

instance
  Natℤ : Nat 𝒰₀ ℤ
  Negativeℤ : Negative 𝒰₀ ℤ

Nat.Constraint Natℤ _ = ⊤
Nat.fromℕ Natℤ n = to-int (n ℤ, 0)
Negative.Constraint Negativeℤ _ = ⊤
Negative.fromNeg Negativeℤ n = to-int (0 ℤ, n)
