{-# OPTIONS --exact-split --safe --prop #-}
module Relation.Binary.Proof where

open import Relation.Binary.Property

open import Universes
open import Proof

module Composable-⊆ {X : 𝒰 ˙}{Y : 𝒱 ˙}{𝒲 𝒯} where
  open MakeComposable (_⊆_ {𝒲 = 𝒲}{𝒯 = 𝒯}{X = X}{Y = Y}) public
  instance
    Composable-⊆-⊆ : {𝒵 : Universe} →
      Composable (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒵)
                 (_⊆_ {𝒲 = 𝒲}{𝒯 = 𝒯}{X = X}{Y = Y})
                 (_⊆_ {𝒲 = 𝒯}{𝒯 = 𝒵}{X = X}{Y = Y})

  Composable.rel Composable-⊆-⊆ = _⊆_
  subrel⊆ (Composable.compose Composable-⊆-⊆ p q) xRy =
    subrel ⦃ q ⦄ $ subrel ⦃ p ⦄ xRy

module Composable-~ {X : 𝒰 ˙}{Y : 𝒱 ˙}{𝒲 𝒯} where
  open MakeComposable (_~_ {𝒲 = 𝒲}{𝒯 = 𝒯}{X = X}{Y = Y}) public
  instance
    Composable-~-~ : {𝒵 : Universe} →
      Composable (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒵)
                 (_~_ {𝒲 = 𝒲}{𝒯 = 𝒯}{X = X}{Y = Y})
                 (_~_ {𝒲 = 𝒯}{𝒯 = 𝒵}{X = X}{Y = Y})
    Composable-⊆-~ : {𝒵 : Universe} →
      Composable (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒵)
                 (_⊆_ {𝒲 = 𝒲}{𝒯 = 𝒯}{X = X}{Y = Y})
                 (_~_ {𝒲 = 𝒯}{𝒯 = 𝒵}{X = X}{Y = Y})
    Composable-~-⊆ : {𝒵 : Universe} →
      Composable (𝒰 ⊔ 𝒱 ⊔ 𝒲 ⊔ 𝒵)
                 (_~_ {𝒲 = 𝒲}{𝒯 = 𝒯}{X = X}{Y = Y})
                 (_⊆_ {𝒲 = 𝒯}{𝒯 = 𝒵}{X = X}{Y = Y})

  Composable.rel Composable-~-~ = _~_
  Composable.compose Composable-~-~ {xRy}{xPy}{xQy} p q = record {
    ~-⊆ = proof xRy 〉 _⊆_ 〉 xPy :by: ~-⊆ ⦃ p ⦄
                    〉 _⊆_ 〉 xQy :by: ~-⊆ ⦃ q ⦄
          qed;
    ~-⊇ = proof xQy 〉 _⊆_ 〉 xPy :by: ~-⊇ ⦃ q ⦄
                    〉 _⊆_ 〉 xRy :by: ~-⊇ ⦃ p ⦄
          qed}

  Composable.rel Composable-~-⊆ = _⊆_
  Composable.compose Composable-~-⊆ {xRy}{xPy}{xQy} p q =
    proof xRy 〉 _⊆_ 〉 xPy :by: ~-⊆ ⦃ p ⦄
              〉 _⊆_ 〉 xQy :by: q
    qed

  Composable.rel Composable-⊆-~ = _⊆_
  Composable.compose Composable-⊆-~ {xRy}{xPy}{xQy} p q =
    proof xRy 〉 _⊆_ 〉 xPy :by: p
              〉 _⊆_ 〉 xQy :by: ~-⊆ ⦃ q ⦄
    qed

