{-# OPTIONS --exact-split --safe --prop #-}
module Data.Functor where

open import Universes
open import Proposition.Identity
open import Function

record Functor (F : (X : 𝒰 ˙) → 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    fmap :
      (f : (x : X) → Y)
      (fx : F X)
      → ------------------
      F Y
    fmap-id : fmap (𝑖𝑑 X) ~ 𝑖𝑑 (F X)
    fmap-∘ :
      (g : Y → Z)
      (f : X → Y)
      → ------------------------------
      fmap (g ∘ f) ~ fmap g ∘ fmap f

open Functor ⦃ … ⦄ public

_<$>_ :
  {F : 𝒰 ˙ → 𝒱 ˙}
  ⦃ r : Functor F ⦄
  {X Y : 𝒰 ˙}
  (f : X → Y)
  (fx : F X)
  → ---------------
  F Y
_<$>_ = fmap

