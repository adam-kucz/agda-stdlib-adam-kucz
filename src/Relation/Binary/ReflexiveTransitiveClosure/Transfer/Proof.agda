{-# OPTIONS --exact-split --safe --prop #-}
open import Relation.Binary.Definition
open import Relation.Binary.Property
open import Relation.Binary.ReflexiveTransitiveClosure.Definition

open import Universes

module Relation.Binary.ReflexiveTransitiveClosure.Transfer.Proof
  {R : BinRel 𝒰 X}
  {single-step : BinRel 𝒱 X}
  (equiv : R ~ refl-trans-close single-step)
  where

open import Proof

