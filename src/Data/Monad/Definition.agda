{-# OPTIONS --exact-split --safe --prop #-}
module Data.Monad.Definition where

open import Universes
open import Type.Sum
open import Proposition.Identity
open import Data.Functor
open import Data.Applicative
open import Function

record Monad
    {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
    (M : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙)
    : ----------------------
    𝒰ω
    where
  field
    ⦃ applicative ⦄ : Applicative M
    join : (m : M (M X)) → M X

  _>>=_ : (m : M X) (f : X → M Y) → M Y
  m >>= f = join (fmap f m)

  field
    ⋆-def : {X : 𝒰 ˙}{Y : 𝒱 ˙}
      (u : M X)(v : M Y)
      → -----------------------
      u ⋆ v == u >>= λ x → fmap (x ,_) v
    associativity : {X : 𝒰 ˙}
      → ----------------------------------------
      join {X = M X} ∘ fmap join == join {X = M X} ∘ join
    unit1 : {X : 𝒰 ˙}
      → ---------------------
      join {X = X} ∘ fmap pure == id
    unit2 : {X : 𝒰 ˙}
      → ---------------------------------
      join {X = X} ∘ pure == id
    -- TODO: prove from other principles
    naturality : ∀ {X : 𝒰 ˙}{Y : 𝒱 ˙}
      (f : X → Y)
      → ----------------------------------
      join ∘ fmap (fmap f) == fmap f ∘ join

open Monad ⦃ … ⦄ renaming (naturality to mon-naturality) public
  
{-# DISPLAY Monad.join M u = join u #-}
{-# DISPLAY Monad._>>=_ M x f = x >>= f #-}
