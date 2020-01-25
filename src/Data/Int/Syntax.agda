{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Syntax where

open import Data.Int.Definition

open import Data.Nat.Definition using (ℕ)
open import Data.Nat.Syntax as N using (Nat)
open N.Pattern

open import PropUniverses
open import Logic using (⊤)
open Logic using (⋆ₚ) public

record Neg 𝒱 (X : 𝒰 ˙) : 𝒰 ⁺ ⊔ 𝒱 ⁺ ˙ where
  field
    Constraint : ℕ → 𝒱 ᵖ
    fromNeg : (n : ℕ) ⦃ _ : Constraint n ⦄ → X

open Neg ⦃ … ⦄ public using (fromNeg)

{-# BUILTIN FROMNEG fromNeg #-}

instance
  Natℤ : Nat 𝒰₀ ℤ
  Nat.Constraint Natℤ _ = ⊤
  Nat.fromℕ Natℤ n = nneg n

  Negℤ : Neg 𝒰₀ ℤ
  Neg.Constraint Negℤ _ = ⊤
  Neg.fromNeg Negℤ 0 = 0
  Neg.fromNeg Negℤ (n +1) = -[ n +1]

module Pattern where
  pattern -[1] = -[ 0 +1]
  pattern -[2] = -[ 1 +1]
  pattern -[3] = -[ 2 +1]
  pattern -[_+2] n = -[ n +1 +1]
  pattern -[_+3] n = -[ n +2 +1]
  
