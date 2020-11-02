{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Property where

open import Data.Int.Definition

open import Type.Sum hiding (_,_)
import Data.Nat as ℕ
open ℕ
open import Proof

ℤ-class-rev : ∀ m n →
  pr₁ (ℤ-class (m ℤ, n))
  ==
  pr₂ (ℤ-class (n ℤ, m))
ℤ-class-rev 0 0 = refl 0
ℤ-class-rev 0 (suc n) = refl 0
ℤ-class-rev (suc m) 0 = refl (suc m)
ℤ-class-rev (suc m) (suc n) = ℤ-class-rev m n

rev-valid : (p : (m ℤ, n) == ℤ-class (m ℤ, n)) → (n ℤ, m) == ℤ-class (n ℤ, m)
rev-valid {0} {0} p = Id.refl (0 ℤ, 0)
rev-valid {0} {suc n} p = Id.refl (suc n ℤ, 0)
rev-valid {suc m} {0} p = Id.refl (0 ℤ, suc m)
rev-valid {suc m} {suc n} p =
  ap2 _ℤ,_ (Id.coe (ap ((suc n) ==_) $ sym $ ℤ-class-rev n m) $ ap pr₂ p)
           (Id.coe (ap ((suc m) ==_) $ ℤ-class-rev m n) $ ap pr₁ p)

open import Data.Nat.Arithmetic.Subtraction.Unsafe
open import Logic

ℤ-class-0-nneg :
  (p : ℤ-class (m ℤ, n) == k ℤ, 0)
  → --------------------------------
  k == m - n ∧ n ≤ m
ℤ-class-0-nneg {0} {0} (Id.refl (0 ℤ, 0)) = refl 0 , z≤ 0
ℤ-class-0-nneg {m +1} {0} (Id.refl (m +1 ℤ, 0)) = Id.refl (m +1) , z≤ m +1
ℤ-class-0-nneg {m +1} {n +1} p with ℤ-class-0-nneg {m}{n} p
... | p₀ , p₁ = p₀ , ap suc p₁

ℤ-class-0-npos :
  (p : ℤ-class (m ℤ, n) == 0 ℤ, k)
  → --------------------------------
  k == n - m ∧ m ≤ n
ℤ-class-0-npos {0} {n} (Id.refl (0 ℤ, n)) = refl n , z≤ n
ℤ-class-0-npos {m +1} {n +1} p with ℤ-class-0-npos {m}{n} p
... | p₀ , p₁ = p₀ , ap suc p₁
