{-# OPTIONS --without-K --exact-split --safe #-}
module Data.Functor where

open import Universes

record Functor (F : (X : 𝒰 ˙) → 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    fmap :
      (f : (x : X) → Y)
      (fx : F X)
      → ------------------
      F Y

open Functor ⦃ … ⦄ public
