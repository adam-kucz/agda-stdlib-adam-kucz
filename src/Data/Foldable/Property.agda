{-# OPTIONS --exact-split --safe --prop #-}
module Data.Foldable.Property where

open import Data.Foldable.Definition

open import Universes
open import Proposition.Identity
open import Proposition.Decidable using (Decidable)
open import Data.Collection
open import Data.Bool

-- TODO: try if it would be better to stay in Decidable rather than Bool
foldable-to-collection :
  (F : (X : 𝒰 ˙) → 𝒱 ˙)
  ⦃ _ : Foldable F ⦄
  ⦃ _ : {x y : X} → Decidable (x == y)⦄
  → ----------------------
  Collection 𝒰₀ (F X) X
_∈_ ⦃ foldable-to-collection F ⦄ x c =
  fold-map ⦃ mon = MonoidOr ⦄ (λ y → to-bool (x == y)) c == true
