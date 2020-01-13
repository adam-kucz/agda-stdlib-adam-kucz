{-# OPTIONS --exact-split --safe --prop #-}
module Data.Maybe where

open import Universes

data Maybe (X : 𝒰 ˙) : 𝒰 ˙ where
  nothing : Maybe X
  just : (x : X) → Maybe X

open import Data.Functor
open import Proposition.Identity

instance
  MaybeFunctor : Functor (Maybe {𝒰})
  fmap ⦃ MaybeFunctor ⦄ _ nothing = nothing
  fmap ⦃ MaybeFunctor ⦄ f (just x) = just (f x)
  fmap-id ⦃ MaybeFunctor ⦄ nothing = refl nothing
  fmap-id ⦃ MaybeFunctor ⦄ (just x) = refl (just x)
  fmap-∘ ⦃ MaybeFunctor ⦄ _ _  nothing = refl nothing
  fmap-∘ ⦃ MaybeFunctor ⦄ g f (just x) = refl (just (g (f x)))

