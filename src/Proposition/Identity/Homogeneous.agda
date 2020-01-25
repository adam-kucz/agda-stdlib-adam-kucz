{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Homogeneous where

open import PropUniverses

open import Proposition.Empty using (¬_)

data Idₚ (X : 𝒰 ˙) : (x y : X) → 𝒰 ᵖ where
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

import Proposition.Identity.Definition as Het

==→het== : {x y : X}(p : x == y) → x Het.== y
==→het== (refl x) = Het.refl x

het==→== : {x y : X}(p : x Het.== y) → x == y
het==→== (Het.refl x) = refl x
