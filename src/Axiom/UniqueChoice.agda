{-# OPTIONS --exact-split --prop #-}
module Axiom.UniqueChoice where

open import PropUniverses
open import Proposition.Sum using (Σₚ; elem)
open import Proposition.Unique
open import Proposition.Identity
open import Logic

postulate
  !choice :
    {𝐴 : (x : X) → 𝒱 ᵖ}
    (!exists : ∃! 𝐴)
    → --------------------------------------------
    Σₚ λ (x : X) → 𝐴 x ∧ ∀ y (p : 𝐴 y) → y == x

!get : Unique X → X
!get x = elem (!choice (! x))
  where ! : Unique X → ∃! λ (x : X) → ⊤
        ! (x , p) = x , (⋆ₚ , λ y _ → p y)

