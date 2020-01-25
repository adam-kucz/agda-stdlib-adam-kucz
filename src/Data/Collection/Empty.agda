{-# OPTIONS --exact-split --prop --safe #-}
module Data.Collection.Empty where

open import Data.Collection.Definition

open import PropUniverses
open import Logic

record Empty
    (Col : 𝒱 ˙)
    (Elem : 𝒰 ˙)
    ⦃ col : Collection 𝒲 Col Elem ⦄
    : ------------------------
    𝒰 ⊔ 𝒱 ⊔ 𝒲 ˙
    where
  field
    ∅ : Col
    _∉∅ : (x : Elem) → x ∉ ∅

open Empty ⦃ … ⦄ public
