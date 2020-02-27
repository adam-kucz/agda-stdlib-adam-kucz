{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Definition where

open import PropUniverses

record Collection 𝒲 (Col : 𝒰 ˙) (Elem : 𝒱 ˙): 𝒰 ⁺ ⊔ 𝒱 ⊔ 𝒲 ⁺ ˙ where
  infix 35 _∈_
  field
    _∈_ : (x : Elem) (c : Col) → 𝒲 ᵖ

open Collection ⦃ … ⦄ public

{-# DISPLAY Collection._∈_ C x l = x ∈ l #-}

open import Proposition.Identity.Definition
open import Logic

infix 35 _∉_
_∉_ :
  {Elem : 𝒰 ˙}
  {Col : 𝒱 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  (x : Elem) (S : Col)
  → -------------------------
  𝒲 ᵖ
x ∉ S = ¬ x ∈ S

infix 35 _⊆_ _⊈_
_⊆_ _⊈_ : {Elem : 𝒰 ˙}{Col : 𝒱 ˙}{Col' : 𝒲 ˙}
  ⦃ col : Collection 𝒯 Col Elem ⦄
  ⦃ col' : Collection 𝒮 Col' Elem ⦄
  (S : Col)(S' : Col')
  → -------------------------
  𝒰 ⊔ 𝒮 ⊔ 𝒯 ᵖ
_⊆_ {Elem = Elem} S S' = ∀ (x : Elem) → x ∈ S → x ∈ S'
S ⊈ S' = ¬ S ⊆ S'

infix 35 _=∅
_=∅ : {Elem : 𝒰 ˙}{Col : 𝒱 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  (S : Col)
  → -------------------------
  𝒰 ⊔ 𝒲 ᵖ
_=∅ {Elem = Elem} S = ¬ ∃ λ (x : Elem) → x ∈ S
