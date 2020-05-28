{-# OPTIONS --exact-split --prop  #-}
module Data.Vec.Functor where

open import Data.Functor
open import Data.Vec.Definition

open import Universes
open import Function hiding (_$_)
open import Logic
open import Proof

open import Data.Vec.Function

open import Axiom.FunctionExtensionality

instance
  VecFunctor : ∀ {n}
    → -------------------------------
    Functor {U = universe-of}(λ — → Vec — n)

fmap ⦃ VecFunctor ⦄ = map
fmap-id ⦃ VecFunctor ⦄ = subrel $ fun-ext go
  where go : ∀ {n} → map id ~ 𝑖𝑑 (Vec X n)
        go [] = refl []
        go (h ∷ v) = ap (h ∷_) (go v)
fmap-∘ ⦃ VecFunctor ⦄ g f = subrel {_P_ = _==_} $ fun-ext go
  where go : ∀ {n} → map {n = n} (g ∘ f) ~ map g ∘ map f
        go [] = refl []
        go (h ∷ v) = ap (g (f h) ∷_) (go v)

