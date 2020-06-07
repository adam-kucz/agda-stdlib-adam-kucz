{-# OPTIONS --exact-split --prop --safe #-}
open import Universes
open import Collection.Definition

module Collection.Nested (X : 𝒰 ˙)(Y : 𝒱 ˙)(Z : 𝒲 ˙) where

open import Collection.Listable

instance
  NestedCollection :
    ⦃ inner : Collection 𝒳 Y X ⦄
    ⦃ outer : Collection 𝒴 Z Y ⦄
    → ----------------------------
    Collection (𝒱 ⊔ 𝒳 ⊔ 𝒴) Z X
  NestedListable  :
    ⦃ list-inner : Listable 𝒳 Y X ⦄
    ⦃ list-outer : Listable 𝒴 Z Y ⦄
    → ----------------------------------------
    Listable (𝒱 ⊔ 𝒳 ⊔ 𝒴) Z X

open import Logic

_∈_ ⦃ NestedCollection ⦄ x c = ∃ λ (y : Y) → x ∈ y ∧ y ∈ c

open import Data.List.Monoid

collection ⦃ NestedListable ⦄ = NestedCollection
to-list ⦃ NestedListable ⦃ list-inner ⦄ ⦄ S =
  fold-map (to-list ⦃ list-inner ⦄) S
⟶ (to-list-valid ⦃ NestedListable ⦄ {S}) (y , (x∈y , y∈S)) =
  ⟵ (∈fold-map to-list S) (y , (y∈S , ⟶ to-list-valid x∈y))
⟵ (to-list-valid ⦃ NestedListable ⦄ {S}) q
  with ⟶ (∈fold-map to-list S) q
⟵ (to-list-valid NestedListable {S}) q | y , (y∈S , x∈to-list-y) =
  y , (⟵ to-list-valid x∈to-list-y , y∈S)

-- open import Collection.Removable

-- -- TODO: implement (needs traversable?)
-- NestedRemovable :
--   ⦃ rem-inner : Removable Y X ⦄
--   → ----------------------------------------
--   Removable Z X
-- remove ⦃ NestedRemovable ⦄ x S = {!!}
-- remove-valid ⦃ NestedRemovable ⦄ = {!!}

