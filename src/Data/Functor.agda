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
      {Y : 𝒱 ˙}
      (f : (x : X) → Y)
      (fx : F X)
      → ------------------
      F Y
    fmap-id : fmap (𝑖𝑑 X) ~ 𝑖𝑑 (F X)
    fmap-∘ : {Y : 𝒱 ˙}{Z : 𝒲 ˙}
      (g : Y → Z)
      (f : X → Y)
      → ------------------------------
      fmap (g ∘ f) ~ fmap g ∘ fmap f

open Functor ⦃ … ⦄ public

infixr 104 _<$>_
_<$>_ :
  {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
  {F : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙}
  ⦃ r : Functor F ⦄
  {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)
  (fx : F X)
  → ---------------
  F Y
_<$>_ = fmap

