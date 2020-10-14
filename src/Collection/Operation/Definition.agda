{-# OPTIONS --exact-split --safe #-}
module Collection.Operation.Definition where

open import Collection.Definition

open import Universes
open import Logic

record Union
    (Col : 𝒱 ˙)
    (Elem : 𝒰 ˙)
    ⦃ col : Collection 𝒲 Col Elem ⦄
    : ------------------------
    𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
    where
  infixl 105 _∪_
  field
    _∪_ : (S₀ S₁ : Col) → Col
    ∪-valid :
      {x : Elem}
      {S₀ S₁ : Col}
      → ------------------------------
      x ∈ S₀ ∪ S₁ ↔ x ∈ S₀ ∨ x ∈ S₁

open Union ⦃ … ⦄ public

record Intersection
    (Col : 𝒱 ˙)
    (Elem : 𝒰 ˙)
    ⦃ col : Collection 𝒲 Col Elem ⦄
    : ------------------------
    𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
    where
  infixl 104 _∩_
  field
    _∩_ : (S₀ S₁ : Col) → Col
    ∩-valid :
      {x : Elem}
      {S₀ S₁ : Col}
      → ------------------------------
      x ∈ S₀ ∩ S₁ ↔ x ∈ S₀ ∧ x ∈ S₁

open Intersection ⦃ … ⦄ public
