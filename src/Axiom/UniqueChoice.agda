{-# OPTIONS --exact-split --prop #-}
module Axiom.UniqueChoice where

open import PropUniverses
open import Proposition.Sum
open import Proposition.Unique
open import Proposition.Unit
open import Proposition.Identity
open import Logic

postulate
  !choice :
    {𝐴 : (x : X) → 𝒱 ᵖ}
    (!exists : ∃! 𝐴)
    → --------------------------------------------
    Σₚ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x

private
  ! : Unique X → ∃! λ (x : X) → ⊤
  ! (x , p) = x , (⋆ₚ , λ y _ → p y)

!get : Unique X → X
!get x = elem (!choice (! x))

!prop : (x : Unique X) (x₁ : X) → x₁ == !get x
!prop x x₁ = ∧right (prop (!choice (! x))) x₁ ⋆ₚ
