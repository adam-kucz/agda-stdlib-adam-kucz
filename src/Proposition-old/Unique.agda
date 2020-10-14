{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Unique where

open import PropUniverses
open import Proposition.Identity using (_==_)
open import Proposition.Sum using (∃)

Unique : (X : 𝒰 ˙) → 𝒰 ᵖ
Unique X = ∃ λ (x : X) → (y : X) → y == x
