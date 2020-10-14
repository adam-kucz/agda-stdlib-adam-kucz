{-# OPTIONS --without-K --exact-split --safe #-}
module Universes where

open import Agda.Primitive public
  renaming ( Level to Universe
           ; lzero to 𝒰₀
           ; lsuc to _⁺
           ; Setω to 𝒰ω)
  using (_⊔_)

infix 1 _˙
Type _˙ : ∀ 𝒰 → Set (𝒰 ⁺)
Type 𝒰 = Set 𝒰
_˙ = Type

𝒰₁ 𝒰₂ : Universe
𝒰₁ = 𝒰₀ ⁺
𝒰₂ = 𝒰₁ ⁺
𝒰₃ = 𝒰₂ ⁺

_⁺⁺ : (𝒰 : Universe) → Universe
𝒰 ⁺⁺ = 𝒰 ⁺ ⁺

variable
  𝒰 𝒱 𝒲 𝒯 𝒮 𝒳 𝒴 𝒵 : Universe
  X Y Z W : 𝒰 ˙
  X₀ X₁ X₂ : 𝒰 ˙
  Y₀ Y₁ Y₂ : 𝒰 ˙
  Z₀ Z₁ Z₂ : 𝒰 ˙
  A B : (x : X) → 𝒱 ˙

record Lift𝒰 {𝒱} (X : 𝒰 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  constructor ↑
  field
    ↓ : X

open Lift𝒰 public

instance
  ↑-inst : ⦃ inst : X ⦄ → Lift𝒰 {𝒱 = 𝒱} X
↑-inst ⦃ inst ⦄ = ↑ inst
