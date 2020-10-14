{-# OPTIONS --without-K --exact-split --safe #-}
module Relation.Binary.Definition where

open import Universes

Rel : (𝒰 : Universe) (X : 𝒱 ˙) (Y : 𝒲 ˙) → 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ˙
Rel 𝒰 X Y = (x : X) (y : Y) → 𝒰 ˙

BinRel : (𝒰 : Universe) (X : 𝒱 ˙) → 𝒰 ⁺ ⊔ 𝒱 ˙
BinRel 𝒰 X = Rel 𝒰 X X

RelProperty : 𝒰ω
RelProperty = {𝒰 𝒱 : Universe} {X : 𝒱 ˙} (R : Rel 𝒰 X X) → 𝒰 ⊔ 𝒱 ˙

