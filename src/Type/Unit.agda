{-# OPTIONS --exact-split --safe --prop #-}
module Type.Unit where

open import Universes

data 𝟙 : 𝒰₀ ˙ where
  instance ⋆ : 𝟙

open import Proposition.Identity

subsingleton : (x y : 𝟙) → x == y
subsingleton ⋆ ⋆ = refl ⋆
