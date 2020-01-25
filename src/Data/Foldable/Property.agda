{-# OPTIONS --exact-split --prop #-}
module Data.Foldable.Property where

open import Data.Foldable.Definition
open import Data.Foldable.Function

open import Universes
open import Proposition.Identity
open import Structure.Monoid
open import Data.List
open import Data.List.Foldable

fold-map==fold-list :
  {F : (X : 𝒰 ˙) → 𝒱 ˙}
  ⦃ _ : Foldable F ⦄
  {Y : 𝒲 ˙}⦃ mon : Monoid Y ⦄
  (f : (x : X) → Y)
  (fx : F X)
  → ------------------------------
  fold-map f fx == fold (fold-map (λ x → [ f x ]) fx)
fold-map==fold-list f fx = ?

open import Proposition.Decidable using (Decidable)
open import Data.Collection hiding (to-list)
open import Data.Bool

-- TODO: try if it would be better to stay in Decidable rather than Bool
foldable-to-collection :
  (F : (X : 𝒰 ˙) → 𝒱 ˙)
  ⦃ _ : Foldable F ⦄
  ⦃ _ : {x y : X} → Decidable (x == y)⦄
  → ----------------------
  Collection 𝒰₀ (F X) X
_∈_ ⦃ foldable-to-collection F ⦄ x c =
  fold-map ⦃ mon = MonoidOr ⦄ (λ y → to-bool (x == y)) c == true

open import Logic

foldable-to-listable :
  (F : (X : 𝒰 ˙) → 𝒱 ˙)
  ⦃ _ : Foldable F ⦄
  ⦃ _ : {x y : X} → Decidable (x == y)⦄
  → ----------------------
  Listable 𝒰₀ (F X) X
collection ⦃ foldable-to-listable F ⦄ = foldable-to-collection F
Listable.to-list (foldable-to-listable F) = to-list
⟶ (to-list-valid ⦃ foldable-to-listable F ⦄) p = {!!}
⟵ (to-list-valid ⦃ foldable-to-listable F ⦄ {S}) q = {!!}
