{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Property where

open import Data.Vec.Definition

open import PropUniverses
open import Proposition.Identity
open import Logic

open import Function

open import Data.Functor

instance
  VecFunctor : ∀ {n}
    → -------------------------------
    Functor {U = universe-of}(λ — → Vec — n)
  fmap ⦃ VecFunctor ⦄ _ [] = []
  fmap ⦃ VecFunctor ⦄ f (h ∷ v) = f h ∷ fmap f v
  fmap-id ⦃ VecFunctor ⦄ [] = refl []
  fmap-id ⦃ VecFunctor ⦄ (h ∷ v) =
    ⟵ Vec== (refl h , fmap-id v)
  fmap-∘ ⦃ VecFunctor ⦄ _ _ [] = refl []
  fmap-∘ ⦃ VecFunctor ⦄ g f (h ∷ v) =
    ⟵ Vec== (refl (g (f h)) , fmap-∘ g f v)
