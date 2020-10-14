{-# OPTIONS --exact-split --safe  #-}
module Type.Decidable.Identity where

open import Type.Decidable.Definition

open import Universes
open import Proof

HasDecidableIdentity : (X : 𝒰 ˙) → 𝒰 ˙
HasDecidableIdentity X = ∀ {x y : X} → Decidable (x == y)

open import Logic
open import Function.Property

apd :
  (f : (x : X) → A x)
  ⦃ inject : Injective f ⦄
  (x y : X)
  ⦃ d : Decidable (x == y) ⦄
  → ----------
  Decidable (f x Het.== f y)
apd f x y ⦃ true p ⦄ = true (ap f p)
-- TODO: remove this redundant instance when Agda fixes #4688
  where instance _ = Relating-all-==-het==
apd f x y ⦃ false ¬p ⦄ = false λ q → ¬p $ inj q
