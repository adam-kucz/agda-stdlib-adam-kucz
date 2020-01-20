{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Definition where

open import PropUniverses

open import Proposition.Empty using (¬_)

data Idₚ (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ᵖ where
  instance refl : (x : X) → Idₚ X X x x

infix 19 _==_
_==_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ᵖ
x == y = Idₚ _ _ x y

{-# DISPLAY Idₚ X Y x y = x == y #-}

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

  subst :
    (𝐴 : (x : X) → 𝒰 ᵖ)
    {x y : X}
    (p : x == y)
    (ax : 𝐴 x)
    → ----------
    𝐴 y
  subst 𝐴 (refl x) ax = ax

  coe :
    (p : 𝑋 == 𝑌)
    (x : 𝑋)
    → ----------
    𝑌
  coe (refl 𝑋) x = x

  coe-eval :
    {𝑋 : 𝒰 ᵖ}
    (p : 𝑋 == 𝑌)
    (x : 𝑋)
    {A : {𝑋 : 𝒰 ᵖ}(x : 𝑋) → 𝒱 ˙}
    (f : {𝑋 : 𝒰 ᵖ}(x : 𝑋) → A x)
    → ---------------
    f (coe p x) == f x
  coe-eval (refl _) x f = refl (f x)
