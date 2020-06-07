{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Arithmetic.Subtraction.Definition where

open import Data.Nat.Definition

open import Data.Nat.Order
open import Data.Nat.Syntax
open Pattern
open import Logic
open import Proof

infixl 130 _-_[_]
_-_[_] : (m n : ℕ)(p : n ≤ m) → ℕ
m - zero [ p ] = m
(m +1) - (n +1) [ p ] = m - n [ ap pred p ]

open import Proposition.Identity hiding (refl)

-== : ∀ {m m' n n' p}
  (q₀ : m == m')
  (q₁ : n == n')
  → -----------------
  m - n [ p ] == m' - n' [ Id.coe (ap2 _≤_ q₁ q₀) p ]
-== (Id.refl m) (Id.refl n) = Id.refl (m - n [ _ ])
