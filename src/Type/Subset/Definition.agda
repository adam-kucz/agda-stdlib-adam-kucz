{-# OPTIONS --exact-split --safe --prop #-}
module Type.Subset.Definition where

open import PropUniverses

Subset : ∀ 𝒰 (X : 𝒱 ˙) → 𝒰 ⁺ ⊔ 𝒱 ˙
Subset 𝒰 X = X → 𝒰 ᵖ

open import Data.Collection
open Data.Collection using (_∈_) public

instance
  SubsetCollection : Collection 𝒰 (Subset 𝒰 X) X
_∈_ ⦃ SubsetCollection ⦄ x c = c x

open import Logic

infixl 105 _∪_
_∪_ :
  (S₀ : Subset 𝒰 X)
  (S₁ : Subset 𝒱 X)
  → ------------------
  Subset (𝒰 ⊔ 𝒱) X
(S₀ ∪ S₁) x = x ∈ S₀ ∨ x ∈ S₁

open import Proposition.Identity

infixr 105 _`_
_`_ : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (f : X → Y)
  (S : Subset 𝒲 X)
  → ----------------
  Subset (𝒰 ⊔ 𝒱 ⊔ 𝒲) Y
(f ` S) y = ∃ λ x → f x == y ∧ x ∈ S
