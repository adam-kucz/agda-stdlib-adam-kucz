{-# OPTIONS --exact-split --safe --prop #-}
module Type.Subset where

open import PropUniverses
open import Type.Sum
open import Proposition.Sum

subset : ∀ 𝒰 (X : 𝒱 ˙) → 𝒱 ⊔ 𝒰 ⁺ ˙
subset 𝒰 X = X → 𝒰 ᵖ

open import Data.Collection

instance
  subsetCollection : Collection 𝒰 (subset 𝒰 X) X
  _∈_ ⦃ subsetCollection ⦄ x c = c x
