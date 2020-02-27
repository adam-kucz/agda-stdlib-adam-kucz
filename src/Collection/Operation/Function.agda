{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Operation.Function where

open import Collection.Operation.Definition

open import Universes
open import Data.List.Definition
open import Collection.Definition
open import Collection.Basic
open import Collection.Listable
open import Structure.Monoid

infixr 108 ⋃_
⋃' : {Col : 𝒱 ˙}{Elem : 𝒰 ˙}{Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ un : Union Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  (s : Col)
  → -------------------------------
  Col
⋃' S s = foldr _∪_ s S
⋃_ : {Col : 𝒱 ˙}{Elem : 𝒰 ˙}{Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ em : Empty Col Elem ⦄
  ⦃ un : Union Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  → -------------------------------
  Col
⋃ S = ⋃' S ∅

infixl 108 ⋂_
⋂' : {Col : 𝒱 ˙}{Elem : 𝒰 ˙}{Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ un : Intersection Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  (s : Col)
  → -------------------------------
  Col
⋂' S s = foldr _∩_ s S
⋂_ :
  {Col : 𝒱 ˙}
  {Elem : 𝒰 ˙}
  {Col' : 𝒯 ˙}
  ⦃ col : Collection 𝒲 Col Elem ⦄
  ⦃ univ : Universal Col Elem ⦄
  ⦃ inter : Intersection Col Elem ⦄
  ⦃ ls' : Listable 𝒳 Col' Col ⦄
  (S : Col')
  → -------------------------------
  Col
⋂ S = ⋂' S Univ

