{-# OPTIONS --safe --exact-split  #-}
open import Universes

module Data.List.Collection {𝒰 : Universe} where

open import Data.List.Definition {𝒰}

data member {X : 𝒰 ˙} (x : X) : (l : List X) → 𝒰₀ ˙ where
  x∈x∷_ : (t : List X) → member x (x ∷ t)
  x∈tail : (h : X) {t : List X} (p : member x t) → member x (h ∷ t)

open import Collection.Definition

instance
  ListCollection : Collection 𝒰₀ (List X) X
  _∈_ ⦃ ListCollection ⦄ = member

{-# DISPLAY member v l = v ∈ l #-}

