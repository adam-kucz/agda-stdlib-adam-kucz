{-# OPTIONS --exact-split --prop  #-}
module Proposition.Decidable.Monoid where

open import Proposition.Decidable.Definition
open import Structure.Monoid.Definition

open import PropUniverses
open import Type.Sum
open import Structure.Monoid.Function
open import Data.Collection
open import Data.Collection.Listable.Function
open import Data.Functor
open import Data.List
open import Data.List.Functor

decidable-fold : {Col : 𝒰 ˙}
  ⦃ list : Listable 𝒲 Col (Σ λ (𝑋 : 𝒱 ᵖ) → Decidable 𝑋) ⦄
  ⦃ mon : Monoid (𝒱 ᵖ) ⦄
  ⦃ edec : Decidable e ⦄
  ⦃ ∙dec : ∀ {x y}
    ⦃ _ : Decidable x ⦄
    ⦃ _ : Decidable y ⦄
    → --------------------
    Decidable (x ∙ y) ⦄
  (S : Col)
  → --------------------------------------
  Decidable (fold-map pr₁ ⦃ mon ⦄ S)
decidable-fold {𝒱 = 𝒱} ⦃ edec = edec ⦄ ⦃ ∙dec ⦄ S = go (to-list S)
  where go : (l : List (Σ λ (𝑋 : 𝒱 ᵖ) → Decidable 𝑋))
           → ----------------------------------------------------------------------
           Decidable (mconcat (pr₁ <$> l))
        go [] = edec
        go ((h , h-dec) ∷ l) = ∙dec {h} {mconcat (pr₁ <$> l)}
          where instance _ = h-dec; _ = go l
