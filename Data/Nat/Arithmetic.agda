{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Arithmetic where

open import PropUniverses
open import Data.Nat.Arithmetic.Definition public
open import Data.Nat.Definition
open import Data.Nat.Syntax
open import Prop'.Function using (_$_)

open import Relation.Binary.Property
open import Operation.Binary.Property

open import Structure.Monoid
open import Structure.Hemiring hiding (_+_; _*_; zero)

open import Prop'.Identity hiding (refl)
open import Prop'.Identity.Property
open import Proof

+-suc : ∀ a b → a + suc b == suc (a + b)
+-suc    zero b = refl (suc b)
+-suc (suc a) b = ap suc $ +-suc a b

instance
  assoc+ : Associative _+_
  assoc ⦃ assoc+ ⦄ zero b c = refl (b + c)
  assoc ⦃ assoc+ ⦄ (suc a) b c = ap suc $ assoc a b c

  0-+ : 0 IsLeftUnitOf _+_
  left-unit ⦃ 0-+ ⦄ = refl

  +-0 : 0 IsRightUnitOf _+_
  right-unit ⦃ +-0 ⦄ 0 = refl 0
  right-unit ⦃ +-0 ⦄ (suc a) = ap suc $ right-unit a

  Commutative+ : Commutative _+_
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

*-0 : (a : ℕ) → a * zero == zero
*-0 zero = refl zero
*-0 (suc a) = *-0 a

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
  comm ⦃ Commutativeℕ* ⦄ zero b = sym $ *-0 b
  comm ⦃ Commutativeℕ* ⦄ (suc a) b = 
    proof b + a * b
      〉 _==_ 〉 b + b * a :by: ap (b +_) $ comm a b
      〉 _==_ 〉 b * suc a :by: sym $ *-suc b a
    qed

  assoc* : Associative _*_
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

  1-* : 1 IsLeftUnitOf _*_
  left-unit ⦃ 1-* ⦄ = right-unit {_∙_ = _+_}

  *-1 : 1 IsRightUnitOf _*_
  *-1 = right-unit-of-commutative-left-unit 1 _*_
  
  Hemiringℕ+* : FormHemiring _+_ _*_ 0
  0* ⦃ Hemiringℕ+* ⦄ _ = refl 0
  *0 ⦃ Hemiringℕ+* ⦄ = *-0
  *[+]==*+* ⦃ Hemiringℕ+* ⦄ = *-+-distrib
  [+]*==*+* ⦃ Hemiringℕ+* ⦄ a b c = 
    proof
      (a + b) * c
        〉 _==_ 〉 c * (a + b)   :by: comm (a + b) c
        〉 _==_ 〉 c * a + c * b :by: *[+]==*+* c a b
        〉 _==_ 〉 c * a + b * c :by: ap (c * a +_) $ comm c b
        〉 _==_ 〉 a * c + b * c :by: ap (_+ b * c) $ comm c a
    qed
