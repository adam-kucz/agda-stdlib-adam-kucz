{-# OPTIONS --exact-split --prop --safe #-}
module Data.Collection.Definition where

open import PropUniverses

record Collection 𝒲 (Col : 𝒰 ˙) (Elem : 𝒱 ˙): 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ⁺ ˙ where
  infix 35 _∈_
  field
    _∈_ : (x : Elem) (c : Col) → 𝒲 ᵖ

open Collection ⦃ … ⦄ public

{-# DISPLAY Collection._∈_ C x l = x ∈ l #-}

open import Proposition.Identity
open import Logic

_∉_ :
  {Elem : 𝒰 ˙}
  {Col : 𝒱 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  (x : Elem) (S : Col)
  → -------------------------
  𝒲 ᵖ
x ∉ S = ¬ x ∈ S

