{-# OPTIONS --safe --exact-split  #-}
module Type.Permutation.Definition where

open import Universes
open import Data.List.Definition
open import Relation.Binary hiding (_~_)

private
  variable
    x y : X
    l l₀ l₁ l₂ : List X

data single-swap {X : 𝒰 ˙} : BinRel 𝒰 (List X) where
  swap : ∀ x y l → single-swap (x ∷ y ∷ l) (y ∷ x ∷ l)
  step : (x : X)(p : single-swap l₀ l₁) → single-swap (x ∷ l₀) (x ∷ l₁)

_~_ : {X : 𝒰 ˙} → BinRel 𝒰 (List X)
_~_ = refl-trans-close single-swap
