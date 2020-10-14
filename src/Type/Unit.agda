{-# OPTIONS --exact-split --safe #-}
module Type.Unit where

open import Universes

record 𝟙 : 𝒰₀ ˙ where
  instance constructor ⋆

{-# BUILTIN UNIT 𝟙 #-}

open import Type.Identity.Definition

subsingleton : (x y : 𝟙) → x == y
subsingleton ⋆ ⋆ = refl ⋆
