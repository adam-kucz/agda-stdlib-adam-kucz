{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinSet where

open import PropUniverses
open import Type.Sum renaming (_,_ to _,,_)
open import Proposition.Sum
open import Proposition.Identity using (_==_; _≠_; refl)
open import Logic
open import Data.Nat
open import Data.List renaming (_∈_ to member)

FinSet : (X : 𝒰 ˙) → 𝒰 ˙

∅ : FinSet X

singleton : (x : X) → FinSet X

infixr 112 _∈_
_∈_ : {X : 𝒰 ˙} (x : X) (l : FinSet X) → 𝒰 ᵖ

toSet :
  ⦃ _ : {x y : X} → Decidable (x == y) ⦄
  (l : List X)
  → -------------------------
  FinSet X



