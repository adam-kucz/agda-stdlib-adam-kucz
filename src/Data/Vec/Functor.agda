{-# OPTIONS --exact-split --prop  #-}
module Data.Vec.Functor where

open import Data.Functor
open import Data.Vec.Definition

open import Universes
open import Function
open import Logic
open import Proof

open import Axiom.FunctionExtensionality

instance
  VecFunctor : ∀ {n}
    → -------------------------------
    Functor {U = universe-of}(λ — → Vec — n)

private
  v-map : ∀ {n}(f : X → Y)(v : Vec X n) → Vec Y n
  v-map _ [] = []
  v-map f (h ∷ v) = f h ∷ v-map f v

fmap ⦃ VecFunctor ⦄ = v-map
fmap-id ⦃ VecFunctor ⦄ = fun-ext go
  where go : ∀ {n} → v-map id ~ 𝑖𝑑 (Vec X n)
        go [] = refl []
        go (h ∷ v) = ap (h ∷_) (go v)
fmap-∘ ⦃ VecFunctor ⦄ g f = fun-ext go
  where go : ∀ {n} → v-map {n = n} (g ∘ f) ~ v-map g ∘ v-map f
        go [] = refl []
        go (h ∷ v) = ap (g (f h) ∷_) (go v)

