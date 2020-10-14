{-# OPTIONS --exact-split --safe #-}
module Data.Nat.Arithmetic.Subtraction.Property where

open import Data.Nat.Arithmetic.Subtraction.Definition

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Arithmetic
open import Data.Nat.Order
open import Data.Nat.Property

open import Operation.Binary hiding (LeftInverse)
open import Logic
open import Proof
open import Function.Proof

-+ : (p : k ≤ m) → m - k + k == m
-+ (z≤ m) = right-unit m
-+ {k +1}{m +1}(s≤s p) = proof m - k + (k +1)
                           === m - k + k +1   :by: +-suc (m - k) k
                           === m +1           :by: ap suc $ -+ p
                         qed

+==→-== :
  (q : m == k + n)
  → ---------------
  m - n == k
+==→-== {_}{k}{0}(Id.refl .(k + 0)) = right-unit k
+==→-== {_}{k}{n +1}(Id.refl .(k + (n +1))) =
  proof k + (n +1) - (n +1)
    === k + n - n           :by: ap (_- (n +1)) $ +-suc k n
    === k                   :by: +==→-== $ Id.refl $ k + n
  qed

-==0 : (p : n ≤ m) → m - n == 0 ↔ m == n
⟶ (-==0 (z≤ _)) q = q
⟶ (-==0 (s≤s p)) q = ap suc $ ⟶ (-==0 p) q
⟵ (-==0 p) (Id.refl m) = +==→-== (Id.refl m)

_-self== : ∀ m → m - m == 0
m -self== = ⟵ (-==0 (refl m)) $ refl m

suc- : (p : n ≤ m)
  → -------------------
  m - n +1 == m +1 - n
suc- (z≤ m) = Id.refl (m +1)
suc- (s≤s p) = suc- p

-+comm : ∀ k
  (p : n ≤ m)
  → -----------------------
  m - n + k == m + k - n
-+comm {n}{m} k p = sym $ +==→-== (
  proof m + k
    === m - n + n + k :by: ap (_+ k) $ sym $ -+ p
    === m - n + k + n :by: swap' (m - n) n k
  qed)

-suc : ∀ m n → m - (n +1) == m - n - 1
-suc m zero = Id.refl (m - 1)
-suc zero (n +1) = Id.refl 0
-suc (m +1) (n +1) = -suc m n

-comm : ∀ m n k → m - n - k == m - k - n
-comm m 0 k = Id.refl (m - k)
-comm m (n +1) 0 = Id.refl (m - (n +1))
-comm zero (n +1) (k +1) = Id.refl 0
-comm (m +1) (n +1) (k +1) =
  proof m - n - (k +1)
    === m - n - k - 1  :by: -suc (m - n) k
    === m - k - n - 1  :by: ap (_- 1) $ -comm m n k
    === m - k - (n +1) :by: sym $ -suc (m - k) n
  qed

open import Function hiding (_$_)

instance
  LeftZeroOf- : 0 IsLeftZeroOf _-_
  RightUnitOf- : 0 IsRightUnitOf _-_
  RelatingSub-≤-≤ : Relating (_- m) _≤_ _≤_
  RelatingSub-≤-≥ : Relating (m -_) _≤_ _≥_
  LeftInverseSub : LeftInverse (_+ m) (_- m)

left-zero ⦃ LeftZeroOf- ⦄ 0 = Id.refl 0
left-zero ⦃ LeftZeroOf- ⦄ (n +1) = Id.refl 0
right-unit ⦃ RightUnitOf- ⦄ = Id.refl
rel-preserv ⦃ RelatingSub-≤-≤ {0} ⦄ p = p
rel-preserv ⦃ RelatingSub-≤-≤ {m +1} ⦄ (z≤ k) = z≤ (k - (m +1))
rel-preserv ⦃ RelatingSub-≤-≤ {m +1} ⦄ (s≤s p) =
  rel-preserv ⦃ RelatingSub-≤-≤ {m} ⦄ p
left-inv ⦃ LeftInverseSub {0} ⦄ = subrel ∘ right-unit
left-inv ⦃ LeftInverseSub {m +1} ⦄ 0 = subrel $ m -self==
left-inv ⦃ LeftInverseSub {m +1} ⦄ (n +1) =
  proof (n +1) + (m +1) - (m +1)
    === n + (m +1) - m           :by: refl _
    === n + m +1 - m             :by: ap (_- m) $ +-suc n m
    === n + m - m +1             :by: sym $ suc- $ postfix (n +_) m
    het== n +1
      :by: ap suc $ left-inv ⦃ LeftInverseSub {m} ⦄ n
  qed

open import Data.Nat.Proof

rel-preserv ⦃ RelatingSub-≤-≥ {m} ⦄ {0}{n} p =
  prefix (_- n) ⦃ Prefix- {n} ⦄ m
rel-preserv ⦃ RelatingSub-≤-≥ ⦄ {a +1}{0} ()
rel-preserv ⦃ RelatingSub-≤-≥ {0} ⦄ {a +1}{b +1} p = refl 0
rel-preserv ⦃ RelatingSub-≤-≥ {m +1} ⦄ {a +1}{b +1}(s≤s p) =
  rel-preserv ⦃ RelatingSub-≤-≥ {m} ⦄ p

-==-↔+==+ :
  (p : n ≤ m)
  (q : l ≤ k)
  → ------------------
  m - n == k - l ↔ m + l == k + n
⟶ (-==-↔+==+ {n}{m}{l}{k} n≤m l≤k) p =
  proof m + l
    === m - n + n + l :by: ap (_+ l) $ sym $ -+ n≤m
    === k - l + n + l :by: ap (λ — → (— + n) + l) p
    === k + n - l + l :by: ap (_+ l) $ -+comm n l≤k
    === k + n         :by: -+ p'
  qed
  where p' : l ≤ k + n
        p' = proof l 〉 _≤_ 〉 k     :by: l≤k
                     〉 _≤_ 〉 k + n :by: postfix (_+ n) k
⟵ (-==-↔+==+ {n}{m}{l}{k} n≤m l≤k) p =
  proof m - n
    === m + l - l - n
      :by: ap (_- n) $ sym $ subrel $ left-inverse-of (_+ l) m
    === k + n - l - n :by: ap (λ — → — - l - n) p
    === k + n - n - l :by: -comm (k + n) l n
    === k - l         :by: ap (_- l) $ subrel $ left-inverse-of (_+ n) k
  qed
