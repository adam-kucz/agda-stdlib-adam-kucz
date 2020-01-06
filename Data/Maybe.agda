{-# OPTIONS --without-K --exact-split --safe #-}
module Data.Maybe where

open import Universes

data Maybe (X : 𝒰 ˙) : 𝒰 ˙ where
  nothing : Maybe X
  just : (x : X) → Maybe X
