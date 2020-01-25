{-# OPTIONS --exact-split --prop #-}
module Data.List.Foldable where

open import Data.List.Definition
open import Data.Foldable.Definition
open import Data.Collection.Listable

open import Universes
open import Structure.Monoid
open import Data.Functor
open import Data.List.Functor
open import Data.List.Collection

instance
  ListFoldable : Foldable {𝒰 = 𝒰} List
  ListListable : Listable 𝒰₀ (List X) X

fold-map ⦃ ListFoldable ⦄ f fx = mconcat (fmap f fx)

open import Logic

collection ⦃ ListListable ⦄ = ListCollection
to-list ⦃ ListListable ⦄ l = l
⟶ (to-list-valid ⦃ ListListable ⦄) p = p
⟵ (to-list-valid ⦃ ListListable ⦄) p = p
