{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Arithmetic.Property where

open import Data.Int.Definition
open import Data.Int.Syntax
open Pattern
open import Data.Int.Arithmetic.Definition
import Data.Nat as ℕ

open import Operation.Binary.Property

instance
  Associativeℤ+ : Associative _+_
  LeftUnitℤ0+ : 0 IsLeftUnitOf _+_
  RightUnitℤ0+ : 0 IsRightUnitOf _+_

open import Proof

left-unit ⦃ LeftUnitℤ0+ ⦄ (nneg n) = Id.refl (nneg n)
left-unit ⦃ LeftUnitℤ0+ ⦄ -[ n +1] = Id.refl -[ n +1]
right-unit ⦃ RightUnitℤ0+ ⦄ (nneg n) = ap nneg $ right-unit n
right-unit ⦃ RightUnitℤ0+ ⦄ -[ n +1] = Id.refl (-[ n +1])

+-suc : (x y : ℤ) → x + (y + 1) == x + y + 1
+-suc (nneg m) (nneg n) = ap nneg $ assoc m n 1
+-suc zero -[ n +1] = left-unit (-[ n +1] + 1)
+-suc (m +1) -one = ap nneg (
  proof ℕ.suc (m ℕ.+ 0)
    === ℕ.suc m :by: ap ℕ.suc (right-unit m) [: _==_ ]
    === m ℕ.+ 1 :by: comm 1 m
  qed)
+-suc (m +1) -[ n +2] = {!+-suc (nneg m) -[ n +1]!}
+-suc -[ m +1] (nneg n) = {!!}
+-suc -[ m +1] -[ n +1] = {!!}

suc-+ : (x y : ℤ) → (x + 1) + y == x + y + 1
suc-+ (nneg m)(nneg n) = ap nneg $ swap' m 1 n 
suc-+ zero -one = refl 0
suc-+ zero -[ n +2] = refl -[ n +1]
suc-+ (m +1) -one = refl (nneg (m ℕ.+ 1))
suc-+ (m +1) -[ n +2] = suc-+ (nneg m) -[ n +1]
suc-+ -one zero = refl 0
suc-+ -one (n +1) = ap nneg $ comm 1 n
suc-+ -one -[ n +1] = refl -[ n +1]
suc-+ -[ m +2] zero = refl -[ m +1]
suc-+ -[ m +2] (n +1) = {!suc-+ -[ m +1] (nneg n)!}
suc-+ -[ m +2] -[ n +1] = refl -[ m ℕ.+ n +2]

assoc ⦃ Associativeℤ+ ⦄ (nneg m)(nneg n)(nneg k) = ap nneg $ assoc m n k
Associative.assoc Associativeℤ+ (nneg m) zero -[ k +1] = 
  ap (λ — → nneg — + -[ k +1]) $ sym $ right-unit m
Associative.assoc Associativeℤ+ (nneg m) (n +1) -one =
  proof nneg (m ℕ.+ n)
    === nneg (m ℕ.+ n ℕ.+1) + -one
      :by: Id.refl _
    === nneg (m ℕ.+ ℕ.suc n) + -one
      :by: ap (λ — → nneg — + -one) $ sym $ ℕ.+-suc m n
  qed
Associative.assoc Associativeℤ+ (nneg m) (n +1) -[ k +2] =
  proof nneg m + (nneg n + -[ k +1])
    === nneg (m ℕ.+ n) + -[ k +1]
      :by: assoc (nneg m)(nneg n) -[ k +1]
    === nneg (m ℕ.+ n ℕ.+1) + -[ k +2]
      :by: Id.refl _
    === nneg (m ℕ.+ ℕ.suc n) + -[ k +2]
      :by: ap (λ — → nneg — + -[ k +2]) $ sym $ ℕ.+-suc m n
  qed
Associative.assoc Associativeℤ+ zero -[ n +1] z = left-unit (-[ n +1] + z)
Associative.assoc Associativeℤ+ (m +1) -one zero =
  ap nneg $ sym $ right-unit m
Associative.assoc Associativeℤ+ (m +1) -one (k +1) =
  ap nneg $ sym $ ℕ.+-suc m k
Associative.assoc Associativeℤ+ (m +1) -one -[ k +1] =
  Id.refl (nneg m + -[ k +1])
Associative.assoc Associativeℤ+ (m +1) -[ n +2] zero =
  sym $ right-unit (nneg m + -[ n +1])
Associative.assoc Associativeℤ+ (m +1) -[ n +2] (k +1) = {!!}
Associative.assoc Associativeℤ+ (m +1) -[ n +2] -[ k +1] = {!!}
Associative.assoc Associativeℤ+ -[ x +1] y z = {!!}
