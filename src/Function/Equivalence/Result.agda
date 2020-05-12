{-# OPTIONS --exact-split --prop #-}
module Function.Equivalence.Result where

open import Function.Equivalence.Definition

open import Universes
open import Function.Basic
open import Operation.Binary
open import Proof

instance
  id-∘ : (𝑖𝑑 X) IsLeftUnitOf (_∘ₛ_ {X = Y})
  ∘-id : (𝑖𝑑 X) IsRightUnitOf (_∘ₛ_ {Z = Y})

left-unit ⦃ id-∘ ⦄ = Id-refl
right-unit ⦃ ∘-id ⦄ = Id-refl
