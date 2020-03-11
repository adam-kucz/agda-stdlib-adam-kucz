{-# OPTIONS --exact-split --prop --safe #-}
module Collection.DecidableSubset where

open import Collection.Definition
open import Collection.Subset

open import Universes
open import Proposition.Decidable

record DecidableSubset 𝒲 (Col : 𝒰 ˙)(Elem : 𝒱 ˙) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  field
    ⦃ subset ⦄ : Subset 𝒲 Col Elem
    ⦃ Decidable∈ ⦄ : {x : Elem}{S : Col} → Decidable (x ∈ S)
