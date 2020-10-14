{-# OPTIONS --exact-split --safe #-}
module Data.Nat.Arithmetic.Subtraction.Definition where

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

infixl 130 _-_
_-_ : (m n : ℕ) → ℕ
m - 0 = m
(m +1) - (n +1) = m - n
-- this case should never come up in actual theorems
0 - (n +1) = 0
