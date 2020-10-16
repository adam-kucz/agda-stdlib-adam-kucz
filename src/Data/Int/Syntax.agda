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
Nat.fromℕ Natℤ n = nneg n
Negative.Constraint Negativeℤ _ = ⊤
Negative.fromNeg Negativeℤ 0 = 0
Negative.fromNeg Negativeℤ (suc n) = -[ n +1]

module Pattern where
  infixl 130 _+1 _+2 _+3
  pattern _+1 n = nneg (suc n)
  pattern _+2 n = (suc n) +1
  pattern _+3 n = (suc n) +2
  pattern -[_+2] n = -[ suc n +1]
  pattern -[_+3] n = -[ suc n +2]
  pattern zero = nneg 0
  pattern one = 0 +1
  pattern two = 0 +2
  pattern three = 0 +3
  pattern -one = -[ 0 +1]
  pattern -two = -[ 0 +2]
  pattern -three = -[ 0 +3]
