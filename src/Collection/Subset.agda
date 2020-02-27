{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Subset where

open import Collection.Definition
open import Collection.Basic
open import Collection.Operation
open import Collection.Insertable
open import Collection.Removable

open import Universes
open import Logic

record Subset 𝒲 (Col : 𝒰 ˙)(Elem : 𝒱 ˙) : (𝒰 ⊔ 𝒱 ⊔ 𝒲) ⁺ ˙ where
  infixl 145 _ᶜ
  field
    ⦃ collection ⦄ : Collection 𝒲 Col Elem
    ⦃ empty ⦄ : Empty Col Elem
    ⦃ universal ⦄ : Universal Col Elem
    ⦃ union ⦄ : Union Col Elem
    ⦃ intersection ⦄ : Intersection Col Elem
    ⦃ insertable ⦄ : Insertable Col Elem
    ⦃ removable ⦄ : Removable Col Elem
    _ᶜ : (X : Col) → Col
    ᶜ-valid : {x : Elem}{X : Col} → x ∈ X ᶜ ↔ x ∉ X

open Subset ⦃ … ⦄ using (_ᶜ; ᶜ-valid) public

module OnSubset {Col : 𝒰 ˙}{Elem : 𝒱 ˙}⦃ _ : Subset 𝒲 Col Elem ⦄ where
  _-_ : (X Y : Col) → Col
  X - Y = X ∩ Y ᶜ

open OnSubset public
