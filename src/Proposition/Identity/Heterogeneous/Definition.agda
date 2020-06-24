{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Heterogeneous.Definition where

open import PropUniverses

open import Proposition.Empty

data Idₚ (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ᵖ where
  refl : (x : X) → Idₚ X X x x

infix 19 _==_ _≡_
_==_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ᵖ
x == y = Idₚ _ _ x y

instance
  refl-inst : {x : X} → x == x
refl-inst = refl _

{-# DISPLAY Idₚ X Y x y = x == y #-}

_≡_ : {X : 𝒰 ˙}
  (x y : X)
  → -------------
  𝒰 ᵖ
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
  𝒰 ᵖ
x ≠ y = ¬ x == y

module Id where
  ap2 : ∀ {K : (x : X)(y : A x) → 𝒲 ˙}
    (f : (x : X)(y : A x) → K x y)
    {x x' y y'}
    (p : x == x')
    (q : y == y')
    → -----------------
    f x y == f x' y'
  ap2 f (refl x) (refl y) = refl (f x y)
