{-# OPTIONS --exact-split --safe --prop #-}
module Relation.Binary.ReflexiveTransitiveClosure.Proof where

open import Relation.Binary.Definition
open import Relation.Binary.ReflexiveTransitiveClosure.Definition

open import Universes
open import Proof.Definition
open Composable

instance
  Composable-R-R* : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    → -----------------
    Composable (𝒰 ⊔ 𝒱) R (refl-trans-close R)
  Composable-R*-R : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    → -----------------
    Composable (𝒰 ⊔ 𝒱) (refl-trans-close R) R

rel (Composable-R-R* {R = R}) = refl-trans-close R
compose Composable-R-R* = step

rel (Composable-R*-R {R = R}) = refl-trans-close R
compose Composable-R*-R {x} {x} {y} (rfl x) q =
  step q (rfl y)
compose Composable-R*-R (step aRb p) q =
  step aRb (compose Composable-R*-R p q)
