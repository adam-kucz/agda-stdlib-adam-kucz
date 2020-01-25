{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Arithmetic where

open import Data.Int.Definition
open import Data.Int.Syntax
open Pattern

open import Universes
open import Data.Nat as ℕ using (ℕ)
open ℕ.Pattern

neg suc pred : (x : ℤ) → ℤ
neg (nneg 0) = nneg 0
neg (nneg (n +1)) = -[ n +1]
neg -[ n +1] = nneg (n +1)

suc (nneg n) = nneg (n +1)
suc -[1] = 0
suc -[ n +2] = -[ n +1]

pred (nneg (n +1)) = nneg n
pred (nneg 0) = -1
pred -[ n +1] = -[ n +2]

abs : (x : ℤ) → ℕ
abs (nneg n) = n
abs -[ n +1] = n +1

infixl 130 _+_ _-_
_+_ _-_ : (x y : ℤ) → ℤ

nneg 0 + y = y
nneg (n₀ +1) + y = suc (nneg n₀ + y)
-[1] + y = pred y
-[ n₀ +2] + y = pred (-[ n₀ +1] + y)

x - y = x + neg y

infixl 140 _*_
_*_ : (x y : ℤ) → ℤ
nneg n₀ * nneg n₁ = nneg (n₀ ℕ.* n₁)
nneg n₀ * -[ n₁ +1] = neg (nneg (n₀ ℕ.* (n₁ +1)))
-[ n₀ +1] * nneg n₁ = neg (nneg ((n₀ +1) ℕ.* n₁))
-[ n₀ +1] * -[ n₁ +1] = nneg ((n₀ +1) ℕ.* (n₁ +1))
