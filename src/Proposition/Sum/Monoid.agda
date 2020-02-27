{-# OPTIONS --exact-split --prop #-}
module Proposition.Sum.Monoid where

open import Proposition.Sum.Definition

open import PropUniverses
open import Proposition.Unit
open import Operation.Binary
open import Logic

open import Axiom.PropositionExtensionality

instance
  ∧-assoc : Associative (_∧_ {𝒰}{𝒰})
  assoc ⦃ ∧-assoc ⦄ _ _ _ = prop-ext
    ((λ { (x , (y , z)) → x , y , z}) ,
     (λ { (x , y , z) → x , (y , z)}))

  ∧-comm : Commutative (_∧_ {𝒰}{𝒰})
  comm ⦃ ∧-comm ⦄ x y = prop-ext
    ((λ {(x , y) → y , x}) ,
     (λ {(y , x) → x , y}))

  ⊤-∧ : ⊤ IsLeftUnitOf (_∧_ {𝒰₀}{𝒰})
  left-unit ⦃ ⊤-∧ ⦄ _ = prop-ext ((λ { (_ , p) → p}) , (λ q → ⋆ₚ , q))

  ∧-⊤ = right-unit-of-commutative-left-unit ⊤ _∧_

  lift-⊤-∧ : Lift𝒰ᵖ ⊤ IsLeftUnitOf (_∧_ {𝒰}{𝒰})
  left-unit ⦃ lift-⊤-∧ ⦄ y = prop-ext ((λ { (_ , p) → p}) , (λ q → ↑prop ⋆ₚ , q))

  lift-∧-⊤ = λ {𝒰} → right-unit-of-commutative-left-unit (Lift𝒰ᵖ ⊤) (_∧_ {𝒰}{𝒰})

  ∨-assoc : Associative (_∨_ {𝒰}{𝒰})
  assoc ⦃ ∨-assoc ⦄ _ _ _ = prop-ext
    ((λ { (∨left p) → ∨left (∨left p)
        ; (∨right (∨left p)) → ∨left (∨right p)
        ; (∨right (∨right q)) → ∨right q}) ,
     λ { (∨left (∨left p)) → ∨left p
       ; (∨left (∨right q)) → ∨right (∨left q)
       ; (∨right q) → ∨right (∨right q)})

  ∨-comm : Commutative (_∨_ {𝒰}{𝒰})
  comm ⦃ ∨-comm ⦄ x y = prop-ext
    ((λ { (∨left p) → ∨right p
        ; (∨right q) → ∨left q}) ,
     λ { (∨left p) → ∨right p
       ; (∨right q) → ∨left q})

  ⊥-∨ : ⊥ IsLeftUnitOf (_∨_ {𝒰₀}{𝒰})
  left-unit ⦃ ⊥-∨ ⦄ _ = prop-ext (
    (λ { (∨right q) → q ; (∨left ()) }) ,
    λ q → ∨right q)

  ∨-⊥ = right-unit-of-commutative-left-unit ⊥ _∨_

  lift-⊥-∨ : Lift𝒰ᵖ ⊥ IsLeftUnitOf (_∨_ {𝒰}{𝒰})
  left-unit ⦃ lift-⊥-∨ ⦄ y = prop-ext (
    (λ { (∨right q) → q; (∨left ())}) ,
    λ q → ∨right q)

  lift-∨-⊥ = λ {𝒰} → right-unit-of-commutative-left-unit (Lift𝒰ᵖ ⊥) (_∨_ {𝒰}{𝒰})

open import Structure.Monoid

Monoid∧ : Monoid (𝒰 ᵖ)
_∙_ ⦃ Monoid∧ ⦄ = _∧_
e ⦃ Monoid∧ ⦄ = Lift𝒰ᵖ ⊤

Monoid∨ : Monoid (𝒰 ᵖ)
_∙_ ⦃ Monoid∨ ⦄ = _∨_
e ⦃ Monoid∨ ⦄ = Lift𝒰ᵖ ⊥

open import Collection
open import Data.List

mconcat∨→elem :
  (l : List (𝒰 ᵖ))
  (p : mconcat ⦃ Monoid∨ ⦄ l)
  → ---------------------------
  ∃ λ 𝑋 → 𝑋 ∧ 𝑋 ∈ l
mconcat∨→elem (h ∷ l) (∨left p) = h , (p , x∈x∷ l)
mconcat∨→elem (h ∷ l) (∨right q) with mconcat∨→elem l q
mconcat∨→elem (h ∷ l) (∨right q) | 𝑋 , (p , 𝑋∈l) = 𝑋 , (p , x∈tail h 𝑋∈l)
