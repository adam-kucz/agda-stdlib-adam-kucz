{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Order where

open import Data.Int.Definition
open import Data.Int.Arithmetic

open import PropUniverses
open import Data.Nat as ℕ using (m; n)

infix 35 _<_ _>_
data _<_ : (x y : ℤ) → 𝒰₀ ᵖ where
  neg<nneg : -[ n +1] < nneg m
  nneg<nneg : (p : n ℕ.< m) → nneg n < nneg m
  neg<neg : (p : m ℕ.< n) → -[ n +1] < -[ m +1]

_>_ : (x y : ℤ) → 𝒰₀ ᵖ
x > y = y < x
