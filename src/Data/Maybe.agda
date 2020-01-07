{-# OPTIONS --without-K --exact-split --safe #-}
module Data.Maybe where

open import Universes
open import Data.Functor

data Maybe (X : 𝒰 ˙) : 𝒰 ˙ where
  nothing : Maybe X
  just : (x : X) → Maybe X

instance
  MaybeFunctor : Functor (Maybe {𝒰})
  fmap ⦃ MaybeFunctor ⦄ _ nothing = nothing
  fmap ⦃ MaybeFunctor ⦄ f (just x) = just (f x)
