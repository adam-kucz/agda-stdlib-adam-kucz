{-# OPTIONS --exact-split --safe --prop #-}
module Data.Applicative where

open import Universes
open import Type.Unit using (𝟙)
open import Type.Sum
open import Proposition.Identity
open import Data.Functor
open import Function

record Applicative
    {U : ∀ {𝒰} → 𝒰 ˙ → Universe}
    (A : ∀ {𝒰}(X : 𝒰 ˙) → U X ˙)
    : ----------------------
    𝒰ω
    where
  infixl 103 _⋆_
  field
    ⦃ functor ⦄ : Functor A
    unit : A 𝟙
    _⋆_ : (x : A X)(y : A Y) → A (X × Y)

  pure : (x : X) → A X
  pure x = fmap (λ _ → x) unit
  infixl 103 _⍟_
  _⍟_ : {X Y : 𝒰 ˙}(f : A (X → Y))(x : A X) → A Y
  f ⍟ x = fmap (uncurry _$_) (f ⋆ x)

  field
    fmap-def : ∀ {X : 𝒰 ˙}(f : X → Y) x → 
      fmap f x == pure f ⍟ x
    naturality : ∀ {X₀ : 𝒰 ˙}{X₁ : 𝒱 ˙}{Y₀ : 𝒲 ˙}{Y₁ : 𝒯 ˙}
      (f : X₀ → X₁)(g : Y₀ → Y₁) u v
      → ---------------------------------------------
      〈 f × g 〉 <$> (u ⋆ v) == fmap f u ⋆ fmap g v
    left-identity : {X : 𝒰 ˙}(v : A X)
      → ------------------------------
      fmap pr₂ (unit ⋆ v) == v
    right-identity : {X : 𝒰 ˙}(u : A X)
      → --------------------------------
      fmap pr₁ (u ⋆ unit) == u
    ⋆-assoc : {X : 𝒰 ˙}{Y : 𝒱 ˙}{Z : 𝒲 ˙}
      (u : A X)(v : A Y)(w : A Z)
      → -------------------------------------------------------------
      fmap Σ-assoc (u ⋆ (v ⋆ w)) == (u ⋆ v) ⋆ w

open Applicative ⦃ … ⦄ public
  
{-# DISPLAY Applicative._⍟_ A u v = u ⍟ v #-}
{-# DISPLAY Applicative._⋆_ A u v = u ⋆ v #-}
