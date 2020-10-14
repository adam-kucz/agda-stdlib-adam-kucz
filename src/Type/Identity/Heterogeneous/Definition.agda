{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Heterogeneous.Definition where

open import Universes

open import Type.Empty

data Id (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ˙ where
  refl : (x : X) → Id X X x x

infix 19 _==_ _≡_
_==_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ˙
x == y = Id _ _ x y

instance
  refl-inst : {x : X} → x == x
refl-inst = refl _

{-# DISPLAY Id X Y x y = x == y #-}

_≡_ : {X : 𝒰 ˙}
  (x y : X)
  → -------------
  𝒰 ˙
_≡_ = _==_

lhs : {X Y : 𝒰 ˙} {x : X} {y : Y} (p : x == y) → X
rhs : {X Y : 𝒰 ˙} {x : X} {y : Y} (p : x == y) → Y

lhs {x = x} _ = x
rhs {y = y} _ = y

infix 19 _≠_
_≠_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ˙
x ≠ y = ¬ x == y

module Id' where
  ap2 : ∀ {K : (x : X)(y : A x) → 𝒲 ˙}
    (f : (x : X)(y : A x) → K x y)
    {x x' y y'}
    (p : x == x')
    (q : y == y')
    → -----------------
    f x y == f x' y'
  ap2 f (refl x) (refl y) = refl (f x y)
