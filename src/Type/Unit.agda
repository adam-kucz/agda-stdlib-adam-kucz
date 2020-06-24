{-# OPTIONS --exact-split --safe --prop #-}
module Type.Unit where

open import Universes

record 𝟙 : 𝒰₀ ˙ where
  instance constructor ⋆

{-# BUILTIN UNIT 𝟙 #-}

open import Proposition.Identity.Definition

subsingleton : (x y : 𝟙) → x == y
subsingleton ⋆ ⋆ = refl ⋆
