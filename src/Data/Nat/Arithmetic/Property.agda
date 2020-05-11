{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Arithmetic.Property where

open import PropUniverses
open import Data.Nat.Arithmetic.Definition
open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern
open import Proposition.Function using (_$_)

open import Relation.Binary.Property hiding (_~_)
open import Operation.Binary.Property

open import Structure.Monoid.Definition
open import Structure.Hemiring hiding (_+_; _*_; zero)

open import Proof

+-suc : ∀ a b → a + suc b == suc (a + b)
+-suc    zero b = refl (suc b)
+-suc (suc a) b = ap suc $ +-suc a b

instance
  assoc+ : Associative _+_
  0-+ : 0 IsLeftUnitOf _+_
  +-0 : 0 IsRightUnitOf _+_
  Commutative+ : Commutative _+_

assoc ⦃ assoc+ ⦄ zero b c = refl (b + c)
assoc ⦃ assoc+ ⦄ (suc a) b c = ap suc $ assoc a b c

left-unit ⦃ 0-+ ⦄ = refl

right-unit ⦃ +-0 ⦄ 0 = refl 0
right-unit ⦃ +-0 ⦄ (suc a) = ap suc $ right-unit a

comm ⦃ Commutative+ ⦄ zero y = sym $ right-unit y
comm ⦃ Commutative+ ⦄ (suc x) y =
  proof suc x + y
    〉 _==_ 〉 suc (y + x) :by: ap suc $ comm x y
    〉 _==_ 〉 y + suc x   :by: sym $ +-suc y x
  qed

*-suc : (a b : ℕ) → a * suc b == a + a * b
*-suc zero _ = refl zero
*-suc (suc a) b = ap suc
  (proof
    b + a * suc b
      〉 _==_ 〉 b + (a + a * b) :by: ap (b +_) $ *-suc a b
      〉 _==_ 〉 a + (b + a * b) :by: swap b a (a * b)
  qed)

private
  *-+-distrib : (a b c : ℕ) → a * (b + c) == a * b + a * c

*-+-distrib zero _ _ = refl zero
*-+-distrib (suc a) b c =
  proof b + c + a * (b + c)
    〉 _==_ 〉 (b + c) + (a * b + a * c)
      :by: ap (b + c +_) $ *-+-distrib a b c
    〉 _==_ 〉 b + (c + (a * b + a * c))
      :by: sym $ assoc b c _
    〉 _==_ 〉 b + (a * b + (c + a * c))
      :by: ap (b +_) $ swap c (a * b) _
    〉 _==_ 〉 b + a * b + (c + a * c)
      :by: assoc b _ _
  qed

instance
  Commutativeℕ* : Commutative _*_
  *-0 : 0 IsRightZeroOf _*_
  0-* : 0 IsLeftZeroOf _*_
  assoc* : Associative _*_
  1-* : 1 IsLeftUnitOf _*_
  *-1 : 1 IsRightUnitOf _*_
  Hemiringℕ+* : FormHemiring _+_ _*_ 0

left-zero ⦃ 0-* ⦄ _ = refl 0

right-zero ⦃ *-0 ⦄ zero = refl zero
right-zero ⦃ *-0 ⦄ (a +1) = right-zero a

comm ⦃ Commutativeℕ* ⦄ zero b = sym $ right-zero b
comm ⦃ Commutativeℕ* ⦄ (suc a) b = 
  proof b + a * b
    〉 _==_ 〉 b + b * a :by: ap (b +_) $ comm a b
    〉 _==_ 〉 b * suc a :by: sym $ *-suc b a
  qed

assoc ⦃ assoc* ⦄ zero _ _ = refl zero
assoc ⦃ assoc* ⦄ (suc a) b c = 
  proof
    b * c + a * (b * c)
      〉 _==_ 〉 b * c + (a * b) * c :by: ap (b * c +_) $ assoc a b c
      〉 _==_ 〉 b * c + c * (a * b) :by: ap (b * c +_) $ comm (a * b) c
      〉 _==_ 〉 c * b + c * (a * b) :by: ap (_+ c * (a * b)) $ comm b c
      〉 _==_ 〉 c * (b + a * b)     :by: sym $ *-+-distrib c b (a * b)
      〉 _==_ 〉 (b + a * b) * c     :by: comm c _
  qed

left-unit ⦃ 1-* ⦄ = right-unit {_∙_ = _+_}

*-1 = right-unit-of-commutative-left-unit 1 _*_
  
*[+]==*+* ⦃ Hemiringℕ+* ⦄ = *-+-distrib
[+]*==*+* ⦃ Hemiringℕ+* ⦄ a b c = 
  proof
    (a + b) * c
      〉 _==_ 〉 c * (a + b)   :by: comm (a + b) c
      〉 _==_ 〉 c * a + c * b :by: *[+]==*+* c a b
      〉 _==_ 〉 c * a + b * c :by: ap (c * a +_) $ comm c b
      〉 _==_ 〉 a * c + b * c :by: ap (_+ b * c) $ comm c a
  qed

Monoid+ : Monoid ℕ
_∙_ ⦃ Monoid+ ⦄ = _+_
e ⦃ Monoid+ ⦄ = 0

Monoid* : Monoid ℕ
_∙_ ⦃ Monoid* ⦄ = _*_
e ⦃ Monoid* ⦄ = 1

open import Logic

¬-+1+-==- : ∀ k m → ¬ k +1 + m == m
¬-+1+-==- k zero ()
¬-+1+-==- k (m +1) p = ¬-+1+-==- k m (
  proof k + m +1
    === k + (m +1) :by: sym $ +-suc k m
    === m          :by: ap pred p
  qed)

open import Function hiding (_$_)
open import Function.Property

+-right-equiv : (_+ m) ~ repeat suc m
+-right-equiv {zero} x = subrel $ right-unit x
+-right-equiv {m +1} x =
  proof x + (m +1)
    〉 _==_ 〉     (x + m) +1        :by: +-suc x m
    〉 Het._==_ 〉 repeat suc m x +1 :by: ap suc $ +-right-equiv {m} x
  qed

+-left-equiv : (m +_) ~ repeat suc m
+-left-equiv {m} x =
  proof m + x
    〉 _==_ 〉 x + m              :by: comm m x
    〉 Het._==_ 〉 repeat suc m x :by: +-right-equiv x
  qed

instance
  Injective-right-+ : Injective (_+ m)
  Injective-left-+ : Injective (m +_)

open import Data.Nat.BasicProperty

Injective-right-+ {m} = injective-equiv (sym $ +-right-equiv)
  where instance _ = injective-repeat suc m

Injective-left-+ {m} = injective-equiv (sym $ +-left-equiv)
  where instance _ = injective-repeat suc m


