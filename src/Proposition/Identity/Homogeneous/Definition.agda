{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Homogeneous.Definition where

open import PropUniverses

open import Proposition.Empty
open import Relation.Binary.Definition

empty-rel : (X : 𝒰 ˙)(Y : 𝒱 ˙) → Rel 𝒰₀ X Y
empty-rel _ _ _ _  = ⊥

data Idₚ (X : 𝒰 ˙) : BinRel 𝒰 X where
  instance refl : (x : X) → Idₚ X x x

infix 19 _==_
_==_ : {X : 𝒰 ˙}(x y : X) → 𝒰 ᵖ
x == y = Idₚ _ x y

{-# DISPLAY Idₚ X Y x y = x == y #-}

lhs : {x y : X}(p : x == y) → X
rhs : {x y : X}(p : x == y) → X

lhs {x = x} _ = x
rhs {y = y} _ = y

infix 19 _≠_
_≠_ : {X : 𝒰 ˙}(x y : X) → 𝒰 ᵖ
x ≠ y = ¬ x == y


