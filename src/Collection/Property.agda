{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Property where

open import Collection.Definition

open import Universes
open import Relation.Binary hiding (_⊆_; Reflexive⊆; Transitive⊆)

instance
  Reflexive⊆ : {Elem : 𝒰 ˙}{Col : 𝒱 ˙}
    ⦃ col : Collection 𝒲 Col Elem ⦄
    → ------------------------------
    Reflexive _⊆_
  Transitive⊆ : {Elem : 𝒰 ˙}{Col : 𝒱 ˙}
    ⦃ col : Collection 𝒲 Col Elem ⦄
    → ------------------------------
    Transitive _⊆_

refl ⦃ Reflexive⊆ ⦄ S x x∈S = x∈S
trans ⦃ Transitive⊆ ⦄ X⊆Y Y⊆Z x x∈X = Y⊆Z x (X⊆Y x x∈X)
