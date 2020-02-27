{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Arithmetic.Definition where

open import Data.Nat.Definition public

infixl 130 _+_
_+_ : (m n : ℕ) → ℕ
zero + n = n
suc m + n = suc (m + n)

infixl 140 _*_
_*_ : (m n : ℕ) → ℕ
zero  * n = zero
suc m * n = n + m * n

open import Data.Nat.Order
open import Proposition.Empty
open import Logic hiding (⊥-recursion)
open import Proof

infixl 130 _-_[_]
_-_[_] : (m n : ℕ)(p : n ≤ m) → ℕ
m - zero [ p ] = m
zero - suc n [ p ] = ⊥-recursion ℕ (f p)
  where f : (p : suc n ≤ 0) → ⊥
        f (∨left ())
        f (∨right ())
suc m - suc n [ p ] = m - n [ ap pred p ]

open import Proposition.Identity hiding (refl)

-== : ∀ {m m' n n' p}
  (q₀ : m == m')
  (q₁ : n == n')
  → -----------------
  m - n [ p ] == m' - n' [ Id.coe (ap2 _≤_ q₁ q₀) p ]
-== (Id.refl m) (Id.refl n) = Id.refl (m - n [ _ ])
