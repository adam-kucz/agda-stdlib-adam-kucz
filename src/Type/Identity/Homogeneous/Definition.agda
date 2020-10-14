{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Homogeneous.Definition where

open import Universes

open import Type.Empty
open import Relation.Binary.Definition

empty-rel : (X : 𝒰 ˙)(Y : 𝒱 ˙) → Rel 𝒰₀ X Y
empty-rel _ _ _ _  = 𝟘

data Id (X : 𝒰 ˙) : BinRel 𝒰 X where
  refl : (x : X) → Id X x x

infix 19 _==_
_==_ : {X : 𝒰 ˙}(x y : X) → 𝒰 ˙
x == y = Id _ x y

instance
  Refl : {x : X} → x == x
Refl {x = x} = refl x

{-# DISPLAY Id X Y x y = x == y #-}

lhs : {x y : X}(p : x == y) → X
rhs : {x y : X}(p : x == y) → X

lhs {x = x} _ = x
rhs {y = y} _ = y

infix 19 _≠_
_≠_ : {X : 𝒰 ˙}(x y : X) → 𝒰 ˙
x ≠ y = ¬ x == y


