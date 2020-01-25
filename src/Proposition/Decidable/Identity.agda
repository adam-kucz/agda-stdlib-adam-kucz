{-# OPTIONS --exact-split --safe --prop  #-}
module Proposition.Decidable.Identity where

open import Proposition.Decidable.Definition

open import PropUniverses
open import Proof

HasDecidableIdentity : (X : 𝒰 ˙) → 𝒰 ˙
HasDecidableIdentity X = ∀ {x y : X} → Decidable (x == y)

open import Proposition.Identity hiding (refl)
open import Logic
open import Function.Property

apd :
  (f : (x : X) → A x)
  ⦃ inject : Injective f ⦄
  (x y : X)
  ⦃ d : Decidable (x == y) ⦄
  → ----------
  Decidable (f x == f y)
apd f x y ⦃ true p ⦄ = true (ap f p)
apd f x y ⦃ false ¬p ⦄ = false λ q → ¬p $ inj q
