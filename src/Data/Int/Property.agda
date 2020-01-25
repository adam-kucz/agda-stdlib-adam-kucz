{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Property where

open import Data.Int.Definition
open import Data.Int.Order

open import Proposition.Decidable
import Data.Nat as ℕ
open import Function.Property
open import Proof

instance
  Injective-nneg : Injective nneg
  inj ⦃ Injective-nneg ⦄ (Id.refl (nneg n)) = refl n

  Injective-[-+1] : Injective -[_+1]
  inj ⦃ Injective-[-+1] ⦄ (Id.refl (-[ n +1])) = refl n

  Decidableℤ== : Decidable (x == y)
  Decidableℤ== {nneg n₀}{nneg n₁} = apd nneg n₀ n₁
  Decidableℤ== {nneg _}{ -[ _ +1]} = false λ ()
  Decidableℤ== { -[ _ +1]}{nneg _} = false λ ()
  Decidableℤ== { -[ n₀ +1]}{ -[ n₁ +1]} = apd -[_+1] n₀ n₁

  Decidableℤ< : Decidable (x < y)
  Decidableℤ< {nneg n₀}{nneg n₁} with decide (n₀ ℕ.< n₁)
  Decidableℤ< {nneg n₀}{nneg n₁} | true p = true (nneg<nneg p)
  Decidableℤ< {nneg n₀}{nneg n₁} | false ¬p = false λ { (nneg<nneg p) → ¬p p }
  Decidableℤ< {nneg n₀}{ -[ n₁ +1]} = false λ ()
  Decidableℤ< { -[ n₀ +1]}{nneg n₁} = true neg<nneg
  Decidableℤ< { -[ n₀ +1]}{ -[ n₁ +1]} with decide (n₁ ℕ.< n₀)
  Decidableℤ< { -[ n₀ +1]} { -[ n₁ +1]} | true p = true (neg<neg p)
  Decidableℤ< { -[ n₀ +1]} { -[ n₁ +1]} | false ¬p = false λ { (neg<neg p) → ¬p p }
