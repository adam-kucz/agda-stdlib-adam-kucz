{-# OPTIONS --exact-split --safe --prop #-}
module Type.Subset where

open import PropUniverses
open import Type.Sum
open import Proposition.Sum

subset : ∀ 𝒰 (X : 𝒱 ˙) → 𝒱 ⊔ 𝒰 ⁺ ˙
subset 𝒰 X = X → 𝒰 ᵖ

_∈_ : (x : X)(p : subset 𝒱 X) → 𝒱 ᵖ
x ∈ p = p x
