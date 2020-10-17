{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Property where

open import Data.Int.Definition

open import Type.Sum hiding (_,_)
import Data.Nat as ℕ
open ℕ using (m; n)
open import Proof

ℤ-class-rev : ∀ m n →
  pr₁ (ℤ-class (m ℤ, n))
  ==
  pr₂ (ℤ-class (n ℤ, m))
ℤ-class-rev 0 0 = refl 0
ℤ-class-rev 0 (ℕ.suc n) = refl 0
ℤ-class-rev (ℕ.suc m) 0 = refl (ℕ.suc m)
ℤ-class-rev (ℕ.suc m) (ℕ.suc n) = ℤ-class-rev m n

rev-valid : (p : (m ℤ, n) == ℤ-class (m ℤ, n)) → (n ℤ, m) == ℤ-class (n ℤ, m)
rev-valid {0} {0} p = Id.refl (0 ℤ, 0)
rev-valid {0} {ℕ.suc n} p = Id.refl (ℕ.suc n ℤ, 0)
rev-valid {ℕ.suc m} {0} p = Id.refl (0 ℤ, ℕ.suc m)
rev-valid {ℕ.suc m} {ℕ.suc n} p =
  ap2 _ℤ,_ (Id.coe (ap ((ℕ.suc n) ==_) $ sym $ ℤ-class-rev n m) $ ap pr₂ p)
           (Id.coe (ap ((ℕ.suc m) ==_) $ ℤ-class-rev m n) $ ap pr₁ p)

