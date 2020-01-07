{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Relation.Unary where

open import PropUniverses

Rel : (𝒰 : Universe) (X : 𝒱 ˙) → 𝒰 ⁺ ⊔ 𝒱 ˙
Rel 𝒰 X = (x : X) → 𝒰 ᵖ

RelProperty : 𝒰ω
RelProperty = {𝒰 𝒱 : Universe} {X : 𝒱 ˙} (R : Rel 𝒰 X) → 𝒰 ⊔ 𝒱 ᵖ

