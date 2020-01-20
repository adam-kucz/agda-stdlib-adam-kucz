{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Comparable where

open import PropUniverses
open import Relation.Binary.Definition
open import Proposition.Identity using (_==_)
open import Logic using (_∨_)

data Comparable {X : 𝒰 ˙} (_<_ : Rel 𝒱 X X) (x y : X) : 𝒰 ⊔ 𝒱 ˙ where
  lt : (p : x < y) → Comparable _<_ x y
  eq : (p : x == y) → Comparable _<_ x y
  gt : (p : y < x) → Comparable _<_ x y

compare :
  ∀ x (_<_ : Rel 𝒱 X X) y
  ⦃ _ : Comparable _<_ x y ⦄
  → Comparable _<_ x y
compare x _<_ y ⦃ ord ⦄ = ord
