{-# OPTIONS --without-K --exact-split --safe --prop #-}
module PropUniverses where

open import Universes public

infix 1 _ᵖ
_ᵖ : ∀ 𝒰 → Set (𝒰 ⁺)
𝒰 ᵖ = Prop 𝒰

variable
  𝑋 𝑌 𝑍 𝑊 : 𝒰 ᵖ
  
record Lift𝒰ᵖ {𝒱} (X : 𝒰 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  constructor ↑prop
  field
    ↓prop : X

open Lift𝒰ᵖ public
