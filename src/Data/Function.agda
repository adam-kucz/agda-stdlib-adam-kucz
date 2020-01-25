{-# OPTIONS --exact-split --safe --prop #-}
module Data.Function where

open import Universes
open import Data.Nat
open import Data.Maybe
open import Data.List
open import Data.Functor

iterate : (m : ℕ)(f : X → Maybe X)(x : X) → Maybe (List X)
iterate 0 _ _ = nothing
iterate (m +1) f x with f x
iterate (m +1) f x | nothing = just []
iterate (m +1) f x | just x' = (x ∷_) <$> iterate m f x'
