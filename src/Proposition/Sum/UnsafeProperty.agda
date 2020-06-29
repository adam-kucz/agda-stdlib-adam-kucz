{-# OPTIONS --exact-split --prop #-}
module Proposition.Sum.UnsafeProperty where

open import PropUniverses
open import Operation.Binary
open import Logic

instance
  ⊤-∨ : ⊤ IsLeftZeroOf _∨_
  ∨-⊤ : ⊤ IsRightZeroOf _∨_
  Lift⊤-∨ : Lift𝒰ᵖ ⊤ IsLeftZeroOf (_∨_ {𝒰}{𝒰})
  ∨-Lift⊤ : Lift𝒰ᵖ ⊤ IsRightZeroOf (_∨_ {𝒰}{𝒰})
  ⊥-∧ : ⊥ IsLeftZeroOf _∧_
  ∧-⊥ : ⊥ IsRightZeroOf _∧_
  Lift⊥-∧ : Lift𝒰ᵖ ⊥ IsLeftZeroOf (_∧_ {𝒰}{𝒰})
  ∧-Lift⊥ : Lift𝒰ᵖ ⊥ IsRightZeroOf (_∧_ {𝒰}{𝒰})

open import Axiom.PropositionExtensionality

left-zero ⦃ ⊤-∨ ⦄ y = prop-ext ((λ _ → ⋆ₚ) , λ _ → ∨left ⋆ₚ) 
right-zero ⦃ ∨-⊤ ⦄ y = prop-ext ((λ _ → ⋆ₚ) , λ _ → ∨right ⋆ₚ) 
left-zero ⦃ Lift⊤-∨ ⦄ y = prop-ext ((λ _ → ↑prop ⋆ₚ) , λ _ → ∨left (↑prop ⋆ₚ))
right-zero ⦃ ∨-Lift⊤ ⦄ y = prop-ext ((λ _ → ↑prop ⋆ₚ) , λ _ → ∨right (↑prop ⋆ₚ))
left-zero ⦃ ⊥-∧ ⦄ y = prop-ext ((λ {((), _)}) , λ ())
right-zero ⦃ ∧-⊥ ⦄ y = prop-ext ((λ {(_ , ())}) , λ ())
left-zero ⦃ Lift⊥-∧ ⦄ y = prop-ext ((λ {(() , _)}) , λ ())
right-zero ⦃ ∧-Lift⊥ ⦄ y = prop-ext ((λ {(_ , ())}) , λ ())
