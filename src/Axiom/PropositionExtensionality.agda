{-# OPTIONS --exact-split --prop #-}
module Axiom.PropositionExtensionality where

open import PropUniverses
open import Proposition.Identity
open import Logic

postulate
  prop-ext : (p : 𝑋 ↔ 𝑌) → 𝑋 == 𝑌

==⊤ : (p : 𝑋) → 𝑋 == ⊤
==⊤ p = prop-ext ((λ _ → ⋆ₚ) , λ _ → p)

==Lift⊤ : (p : 𝑋) → 𝑋 == Lift𝒰ᵖ ⊤
==Lift⊤ p = prop-ext ((λ _ → ↑prop ⋆ₚ) , λ _ → p)

==⊥ : (¬p : ¬ 𝑋) → 𝑋 == ⊥
==⊥ ¬p = prop-ext (¬p , (λ ()))

==Lift⊥ : (¬p : ¬ 𝑋) → 𝑋 == Lift𝒰ᵖ ⊥
==Lift⊥ ¬p = prop-ext ((λ p → ↑prop (¬p p)) , (λ ()))
