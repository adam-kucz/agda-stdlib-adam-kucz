{-# OPTIONS --exact-split --safe --prop #-}
module Prop'.Identity.Definition where

open import PropUniverses

open import Prop'.Empty using (¬_)

data Idₚ (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ᵖ where
  instance refl : (x : X) → Idₚ X X x x

infix 19 _==_
_==_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ᵖ
x == y = Idₚ _ _ x y

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
  -- more general than Relation.Binary.Property.sym
  -- it doesn't require the two sides
  -- to be of the same type
  sym : {x : X} {y : Y}
    (p : x == y)
    → ----------
    y == x
  sym (refl x) = refl x

  transport :
    (𝐴 : (x : X) → 𝒰 ᵖ)
    {x y : X}
    (p : x == y)
    (ax : 𝐴 x)
    → ----------
    𝐴 y
  transport 𝐴 (refl x) ax = ax
