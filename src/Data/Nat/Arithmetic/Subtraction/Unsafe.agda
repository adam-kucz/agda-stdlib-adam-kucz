{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Arithmetic.Subtraction.Unsafe where

open import Data.Nat.Definition
open import Data.Nat.Order
open import Data.Nat.Syntax
open Pattern

infixl 130 _-_
_-_ : (m n : ℕ) → ℕ
m - 0 = m
0 - (n +1) = 0
(m +1) - (n +1) = m - n

open import Data.Nat.Arithmetic.Subtraction.Definition
open import Proof

unsafe-is-safe : ∀{m n}(p : n ≤ m) → m - n == (m - n [ p ])
unsafe-is-safe {m}{zero} p = Id.refl m
unsafe-is-safe {m +1}{n +1} p = unsafe-is-safe {m} $ ap pred p

open import Function hiding (_$_)
open import Data.Nat.Arithmetic.Definition

_-self==0 : ∀ m → m - m == 0
0 -self==0 = Id.refl zero
(m +1) -self==0 = m -self==0

open import Function.Proof
open import Operation.Binary hiding (LeftInverse)

instance
  LeftZeroOf- : 0 IsLeftZeroOf _-_
  RightUnitOf- : 0 IsRightUnitOf _-_
  LeftInverseUnsafeSub : LeftInverse (_+ m) (_- m)

left-zero ⦃ LeftZeroOf- ⦄ zero = Id.refl 0
left-zero ⦃ LeftZeroOf- ⦄ (y +1) = Id.refl 0

right-unit ⦃ RightUnitOf- ⦄ = Id.refl

open import Data.Nat.Arithmetic.Property
left-inv ⦃ LeftInverseUnsafeSub {m} ⦄ zero = subrel $ m -self==0
left-inv ⦃ LeftInverseUnsafeSub {0} ⦄ (n +1) = subrel $ right-unit (n +1)
left-inv ⦃ LeftInverseUnsafeSub {m +1} ⦄ (n +1) =
  subrel {sub = _==_} (
  proof n + (m +1) - m
    === (n +1) + m - m
      :by: ap (_- m) $ +-suc n m
    === n +1
      :by: subrel $ left-inv ⦃ LeftInverseUnsafeSub {m} ⦄ (n +1)
  qed)

-suc : ∀ a b →
  a - suc b == a - b - 1
-suc a zero = Id.refl (a - 1)
-suc zero (b +1) = Id.refl 0
-suc (a +1) (b +1) = -suc a b

-comm : ∀ a b c →
  a - b - c == a - c - b
-comm a b zero = Id.refl (a - b)
-comm a zero (c +1) = Id.refl (a - (c +1))
-comm zero (b +1) (c +1) = Id.refl 0
-comm (a +1) (b +1) (c +1) =
  proof a - b - (c +1)
    === a - b - c - 1
      :by: -suc (a - b) c
    === a - c - b - 1
      :by: ap (_- 1) $ -comm a b c
    === a - c - (b +1)
      :by: sym $ -suc (a - c) b
  qed

open import PropUniverses

unsafe-prop-from-safe :
  (𝐴 : ℕ → 𝒰 ᵖ)
  (p : m ≤ n)
  (q : 𝐴 (n - m [ p ]))
  → ----------------------
  𝐴 (n - m)
unsafe-prop-from-safe 𝐴 p q =
  Id.coe (ap 𝐴 $ sym $ unsafe-is-safe p) q

-+ : ∀ m n k → m - (n + k) == m - n - k
-+ m 0 k = refl (m - k)
-+ 0 (n +1) k = sym $ left-zero k
-+ (m +1) (n +1) k = -+ m n k

*- : ∀ m n k → m * (n - k) == m * n - m * k
*- m n 0 = proof m * n
             === m * n - 0     :by: refl (m * n)
             === m * n - m * 0 :by: ap (m * n -_) $ sym $ right-zero m
           qed
*- m 0 (k +1) = proof m * 0
                  === 0                  :by: right-zero m
                  === 0 - m * (k +1)     :by: sym $ left-zero (m * (k +1))
                  === m * 0 - m * (k +1)
                    :by: ap (_- m * (k +1)) $ sym $ right-zero m
                qed
*- m (n +1) (k +1) =
  proof m * (n - k)
    === m * n - m * k           :by: *- m n k
    === m * n + m - m - m * k
      :by: ap (_- m * k) $ sym $ subrel $ left-inverse-of (_+ m) (m * n)
    === m + m * n - m - m * k   :by: ap (λ — → — - m - m * k) $ comm (m * n) m
    === m + m * n - (m + m * k) :by: sym $ -+ (m + m * n) m (m * k)
    === m * (n +1) - m * (k +1) :by: sym $ ap2 _-_ (*-suc m n) (*-suc m k)
  qed

double- : ∀ m n k (p : k ≤ n) → m - (n - k) == m + k - n
double- m n 0 p = ap (_- n) $ sym $ right-unit m
double- m (n +1) (k +1) p =
  proof m - (n - k)
    === m + k - n           :by: double- m n k (ap pred p)
    === m + (k +1) - (n +1) :by: ap (_- (n +1)) $ sym $ +-suc m k
  qed

instance
  RelatingUnsafeSub-≤-≤ : Relating (_- m) _≤_ _≤_
  -- RelatingUnsafeSub-≤-≥ : Relating (m -_) _≤_ _≥_

rel-preserv ⦃ RelatingUnsafeSub-≤-≤ {n} ⦄ (z≤ m) =
  proof 0 - n
    === 0        :by: left-zero n [: _==_ ]
    〉 _≤_ 〉 m - n :by: z≤ (m - n)
  qed
rel-preserv ⦃ RelatingUnsafeSub-≤-≤ {zero} ⦄ q@(s≤s _) = q
rel-preserv ⦃ RelatingUnsafeSub-≤-≤ {k +1} ⦄ (s≤s {n} {m} n≤m) =
  rel-preserv ⦃ RelatingUnsafeSub-≤-≤ {k} ⦄ n≤m

