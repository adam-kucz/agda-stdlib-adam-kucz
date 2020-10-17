{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Arithmetic.Property where

open import Data.Int.Definition
open import Data.Int.Syntax
open import Data.Int.Arithmetic.Definition

open import Type.Sum hiding (_,_)
import Data.Nat as ℕ
open ℕ using (ℕ; m; n)
open import Operation.Binary.Property

private
  instance
    Associative+ℕ×ℕ : Associative _+ℕ×ℕ_
    Commutative+ℕ×ℕ : Commutative _+ℕ×ℕ_
    LeftUnit[0,0]+ℕ×ℕ : (0 ℤ, 0) IsLeftUnitOf _+ℕ×ℕ_
    RightUnit[0,0]+ℕ×ℕ : (0 ℤ, 0) IsRightUnitOf _+ℕ×ℕ_

open import Proof

assoc ⦃ Associative+ℕ×ℕ ⦄ (m₀ ℤ, m₁)(n₀ ℤ, n₁)(k₀ ℤ, k₁) =
  ap2 _ℤ,_ (assoc m₀ n₀ k₀) (assoc m₁ n₁ k₁)
left-unit ⦃ LeftUnit[0,0]+ℕ×ℕ ⦄ (m₀ ℤ, m₁) =
  ap2 _ℤ,_ (left-unit m₀) (left-unit m₁)
right-unit ⦃ RightUnit[0,0]+ℕ×ℕ ⦄ (m₀ ℤ, m₁) =
  ap2 _ℤ,_ (right-unit m₀) (right-unit m₁)
comm ⦃ Commutative+ℕ×ℕ ⦄ (m₀ ℤ, m₁)(n₀ ℤ, n₁) = 
  ap2 _ℤ,_ (comm m₀ n₀) (comm m₁ n₁)

open import Type.Quotient

open Property checked-+ hiding (LeftInverse⊙; RightInverse⊙) public

instance
  LeftInverse+ℕ×ℕ : LeftInverse -_ _+_
  RightInverse+ℕ×ℕ : RightInverse -_ _+_

open import Proposition.Sum
open import Data.Nat.Arithmetic.Subtraction.Unsafe
  renaming (_-_ to _ℕ-_)

private instance _ = ℤ-impl

left-inverse ⦃ LeftInverse+ℕ×ℕ ⦄ (m ℤ, n , _) = Σₚ== (
  proof class-of (n ℕ.+ m ℤ, m ℕ.+ n)
    === n ℕ.+ m ℕ- (m ℕ.+ n) ℤ, 0
      :by: ℤ-class-nneg p
    === 0 ℤ, 0
      :by: ap (_ℤ, 0){r = _==_}{a = n ℕ.+ m ℕ- (m ℕ.+ n)} (
        proof n ℕ.+ m ℕ- (m ℕ.+ n)
          === n ℕ.+ m ℕ- (n ℕ.+ m) :by: ap (n ℕ.+ m ℕ-_) $ comm m n
          === 0                    :by: (n ℕ.+ m) -self==0
        qed)
  qed)
  where p : m ℕ.+ n ℕ.≤ n ℕ.+ m
        p = Id.coe (ap (m ℕ.+ n ℕ.≤_) $ comm m n) $
            refl {R = ℕ._≤_} (m ℕ.+ n)
right-inverse ⦃ RightInverse+ℕ×ℕ ⦄ x =
  proof x + - x
    === - x + x          :by: comm x (- x)
    === as-quot (0 ℤ, 0) :by: left-inverse x
  qed
