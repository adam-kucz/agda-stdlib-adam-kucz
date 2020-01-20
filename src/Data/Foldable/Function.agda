{-# OPTIONS --exact-split --prop #-}
module Data.Foldable.Function where

open import Data.Foldable.Definition

open import Universes
open import Function.Structure

foldr :
  {F : 𝒰 ˙ → 𝒱 ˙}
  ⦃ _ : Foldable F ⦄
  (f : X → Y → Y)
  (z : Y)
  → --------------------
  (fx : F X) → Y
foldr f z fx = fold-map ⦃ mon = EndoMonoid ⦄ f fx z

open import Function using (flip)
open import Structure.Monoid using (dual)

foldl :
  {F : 𝒰 ˙ → 𝒱 ˙}
  ⦃ _ : Foldable F ⦄
  (f : Y → X → Y)
  (z : Y)
  → --------------------
  (fx : F X) → Y
foldl f z fx = fold-map ⦃ mon = dual EndoMonoid ⦄ (flip f) fx z
