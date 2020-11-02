{-# OPTIONS --exact-split --safe #-}
module Data.Int.Arithmetic where

open import Data.Int.Definition
open import Data.Int.Syntax
open Pattern
import Data.Nat as ℕ

infixr 135 -_
-_ : (x : ℤ) → ℤ
- zero = zero
- (x +1) = -[ x +1]
- -[ x +1] = x +1

infixl 130 _+_ _-_
_+_ _-_ : (x y : ℤ) → ℤ

nneg m + nneg n = nneg (m ℕ.+ n)
zero + -[ n +1] = -[ n +1]
m +1 + -one = nneg m
m +1 + -[ n +2] = nneg m + -[ n +1]
-[ m +1] + zero = -[ m +1]
-one + (n +1) = nneg n
-[ m +2] + (n +1) = -[ m +1] + nneg n
-[ m +1] + -[ n +1] = -[ m ℕ.+ n +2]

x - y = x + - y
