{-# OPTIONS --exact-split --safe --prop #-}
module Prop'.Unique where

open import PropUniverses
open import Prop'.Identity using (_==_)
open import Prop'.Sum using (∃)

Unique : (X : 𝒰 ˙) → 𝒰 ᵖ
Unique X = ∃ λ (x : X) → (y : X) → y == x
