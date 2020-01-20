{-# OPTIONS --exact-split --prop #-}
module Function.Structure where

open import Function.Basic

open import Universes
open import Proposition.Identity
open import Operation.Binary

open import Axiom.FunctionExtensionality

instance
  ∘ₛ-assoc : Associative (_∘ₛ_ {Y = Y})
  assoc ⦃ ∘ₛ-assoc ⦄ h g f = fun-ext λ x → refl (h $ g $ f x)

  id-∘ₛ : (𝑖𝑑 X) IsLeftUnitOf (_∘ₛ_ {X = Y})
  left-unit ⦃ id-∘ₛ ⦄ f = fun-ext λ x → refl (f x)

  ∘ₛ-id : (𝑖𝑑 X) IsRightUnitOf (_∘ₛ_ {Z = Y})
  right-unit ⦃ ∘ₛ-id ⦄ f = fun-ext λ x → refl (f x)

open import Structure.Monoid

EndoMonoid : Monoid (X → X)
_∙_ ⦃ EndoMonoid ⦄ = _∘ₛ_
e ⦃ EndoMonoid ⦄ = id
