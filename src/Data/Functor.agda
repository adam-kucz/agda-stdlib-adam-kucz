{-# OPTIONS --exact-split --safe --prop #-}
module Data.Functor where

open import Universes
open import Proposition.Identity
open import Function

record Functor
    {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
    (F : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙)
    : ----------------------
    𝒰ω
    where
  field
    fmap :
      {X : 𝒰 ˙}{Y : 𝒱 ˙}
      (f : (x : X) → Y)
      (fx : F X)
      → ------------------
      F Y
    fmap-id : fmap (𝑖𝑑 X) == 𝑖𝑑 (F X)
    fmap-∘ : {Y : 𝒱 ˙}{Z : 𝒲 ˙}
      (g : Y → Z)
      (f : X → Y)
      → ------------------------------
      fmap (g ∘ f) == fmap g ∘ fmap f

  infixr 104 _<$>_
  _<$>_ = fmap

open Functor ⦃ … ⦄ public

{-# DISPLAY Functor.fmap F f = fmap f #-}
