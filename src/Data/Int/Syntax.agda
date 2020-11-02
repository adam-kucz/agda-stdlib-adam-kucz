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

data ℤ' : 𝒰₀ ˙ where
  nneg -[_+1] : (m : ℕ) → ℤ'

ℤ→ℤ' : ℤ → ℤ'
ℤ'→ℤ : ℤ' → ℤ

open import Proposition.Empty
open import Proposition.Decidable
import Data.Nat as ℕ
open import Data.Nat.Arithmetic.Subtraction.Unsafe
open import Relation.Binary
open import Logic hiding (⊥-recursion)
open import Proof

ℤ→ℤ' (0 ℤ, n , p) = nneg 0
ℤ→ℤ' (suc m ℤ, 0 , p) = nneg (suc m)
ℤ→ℤ' (suc m ℤ, suc n , p) = ⊥-recursion ℤ' contr
  where contr : ⊥
        contr with decide (n ℕ.≤ m)
        ... | true q with () ←
          proof suc m ℤ, suc n
            === ℤ-class (m ℤ, n) :by: p
            === m - n ℤ, 0       :by: ⟶ ℤ-class-nneg q [: _==_ ]
          qed
        ... | false ¬q with () ←
          proof suc m ℤ, suc n
            === ℤ-class (m ℤ, n) :by: p
            === 0 ℤ, n - m
              :by: ⟶ ℤ-class-npos $ total-other ¬q [: _==_ ]
          qed
ℤ'→ℤ (nneg 0) = (0 ℤ, 0 , Id.refl (0 ℤ, 0))
ℤ'→ℤ (nneg (suc m)) = (suc m ℤ, 0 , Id.refl (suc m ℤ, 0))
ℤ'→ℤ -[ m +1] = (0 ℤ, suc m , Id.refl (0 ℤ, suc m))

instance
  Natℤ' : Nat 𝒰₀ ℤ'
  Negativeℤ' : Negative 𝒰₀ ℤ'

Nat.Constraint Natℤ' _ = ⊤
Nat.fromℕ Natℤ' n = ℤ→ℤ' (fromℕ n)
Negative.Constraint Negativeℤ' _ = ⊤
Negative.fromNeg Negativeℤ' n = ℤ→ℤ' (fromNeg n)

module Patterns where
  pattern _+1 n = nneg (suc n)
  pattern _+2 n = suc n +1
  pattern _+3 n = suc n +1
  pattern zero = nneg 0
  pattern one = nneg 1
  pattern two = nneg 2
  pattern -[_+2] n = -[ suc n +1]
  pattern -[_+3] n = -[ suc n +2]
  pattern -one = -[ 0 +1]
  pattern -two = -[ 0 +2]
