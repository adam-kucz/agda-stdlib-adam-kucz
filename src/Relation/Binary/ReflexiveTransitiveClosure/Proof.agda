{-# OPTIONS --exact-split --safe --prop #-}
module Relation.Binary.ReflexiveTransitiveClosure.Proof where

open import Relation.Binary.Definition
open import Relation.Binary.ReflexiveTransitiveClosure.Definition
  renaming (refl-trans-close to rtc)

open import Universes
open import Proof.Definition
open Composable

private
  module R*Comp {𝒰}{X : 𝒰 ˙}{R : BinRel 𝒱 X} where
    open MakeTransComposable (rtc R) public

instance
  Composable-R-R* : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    → -----------------
    Composable (𝒰 ⊔ 𝒱) R (rtc R)
  Composable-R*-R : {X : 𝒰 ˙}
    {R : Rel 𝒱 X X}
    → -----------------
    Composable (𝒰 ⊔ 𝒱) (rtc R) R

Composable-R-R* {R = R} = Composable-sub-R-P (rtc R) R (rtc R)

Composable-R*-R {R = R} = Composable-R-sub-P (rtc R) (rtc R) R

open import Relation.Binary.Property

Composable-R-R : {X : 𝒰 ˙}
  (R : Rel 𝒱 X X)
  → -----------------
  Composable (𝒰 ⊔ 𝒱) R R
Composable-R-R R = Composable-sub-R-sub-P (rtc R) R (rtc R) R

