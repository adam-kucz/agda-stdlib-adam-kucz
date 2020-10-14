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
  ∧-comm : Commutative (_∧_ {𝒰}{𝒰})
  ⊤-∧ : ⊤ IsLeftUnitOf (_∧_ {𝒰₀}{𝒰})
  ∧-⊤ : ⊤ IsRightUnitOf (_∧_ {𝒰}{𝒰₀})
  lift-⊤-∧ : Lift𝒰ᵖ ⊤ IsLeftUnitOf (_∧_ {𝒰}{𝒰})
  ∧-lift-⊤ : Lift𝒰ᵖ ⊤ IsRightUnitOf (_∧_ {𝒰}{𝒰})
  ⊥-∧ : ⊥ IsLeftZeroOf (_∧_ {𝒰₀}{𝒰₀})
  ∧-⊥ : ⊥ IsRightZeroOf (_∧_ {𝒰₀}{𝒰₀})
  lift-⊥-∧ : Lift𝒰ᵖ ⊥ IsLeftZeroOf (_∧_ {𝒰}{𝒰})
  ∧-lift-⊥ : Lift𝒰ᵖ ⊥ IsRightZeroOf (_∧_ {𝒰}{𝒰})

assoc ⦃ ∧-assoc ⦄ _ _ _ = prop-ext
  ((λ { (x , (y , z)) → x , y , z}) ,
   (λ { (x , y , z) → x , (y , z)}))

comm ⦃ ∧-comm ⦄ x y = prop-ext
  ((λ {(x , y) → y , x}) ,
   (λ {(y , x) → x , y}))

left-unit ⦃ ⊤-∧ ⦄ _ = prop-ext (∧right , (⋆ₚ ,_))
right-unit ⦃ ∧-⊤ ⦄ _ = prop-ext (∧left , (_, ⋆ₚ))
left-unit ⦃ lift-⊤-∧ ⦄ y = prop-ext (∧right , (↑prop ⋆ₚ ,_))
∧-lift-⊤ {𝒰} = right-unit-of-commutative-left-unit (Lift𝒰ᵖ ⊤) (_∧_ {𝒰}{𝒰})

left-zero ⦃ ⊥-∧ ⦄ _ = prop-ext (∧left , λ ())
∧-⊥ = right-zero-of-commutative-left-zero ⊥ _∧_
left-zero ⦃ lift-⊥-∧ ⦄ y = prop-ext (∧left , λ ())
∧-lift-⊥ {𝒰} = right-zero-of-commutative-left-zero (Lift𝒰ᵖ ⊥) (_∧_ {𝒰}{𝒰})

instance
  ∨-assoc : Associative (_∨_ {𝒰}{𝒰})
  ∨-comm : Commutative (_∨_ {𝒰}{𝒰})
  ⊥-∨ : ⊥ IsLeftUnitOf (_∨_ {𝒰₀}{𝒰})
  ∨-⊥ : ⊥ IsRightUnitOf (_∨_ {𝒰}{𝒰₀})
  lift-⊥-∨ : Lift𝒰ᵖ ⊥ IsLeftUnitOf (_∨_ {𝒰}{𝒰})
  ∨-lift-⊥ : Lift𝒰ᵖ ⊥ IsRightUnitOf (_∨_ {𝒰}{𝒰})
  ⊤-∨ : ⊤ IsLeftZeroOf (_∨_ {𝒰₀}{𝒰₀})
  ∨-⊤ : ⊤ IsRightZeroOf (_∨_ {𝒰₀}{𝒰₀})
  lift-⊤-∨ : Lift𝒰ᵖ ⊤ IsLeftZeroOf (_∨_ {𝒰}{𝒰})
  ∨-lift-⊤ : Lift𝒰ᵖ ⊤ IsRightZeroOf (_∨_ {𝒰}{𝒰})

assoc ⦃ ∨-assoc ⦄ _ _ _ = prop-ext
  ((λ { (∨left p) → ∨left (∨left p)
      ; (∨right (∨left p)) → ∨left (∨right p)
      ; (∨right (∨right q)) → ∨right q}) ,
   λ { (∨left (∨left p)) → ∨left p
     ; (∨left (∨right q)) → ∨right (∨left q)
     ; (∨right q) → ∨right (∨right q)})

comm ⦃ ∨-comm ⦄ x y = prop-ext
  ((λ { (∨left p) → ∨right p
      ; (∨right q) → ∨left q}) ,
   λ { (∨left p) → ∨right p
     ; (∨right q) → ∨left q})

left-unit ⦃ ⊥-∨ ⦄ _ = prop-ext (
  (λ { (∨right q) → q; (∨left ())}) , ∨right)
right-unit ⦃ ∨-⊥ ⦄ _ = prop-ext (
  (λ { (∨left p) → p; (∨right ())}) , ∨left)
left-unit ⦃ lift-⊥-∨ ⦄ y = prop-ext (
  (λ { (∨right q) → q; (∨left ())}) , ∨right)
∨-lift-⊥ {𝒰} = right-unit-of-commutative-left-unit (Lift𝒰ᵖ ⊥) (_∨_ {𝒰}{𝒰})

left-zero ⦃ ⊤-∨ ⦄ _ = prop-ext ((λ _ → ⋆ₚ) , ∨left)
∨-⊤ = right-zero-of-commutative-left-zero ⊤ _∨_
left-zero ⦃ lift-⊤-∨ ⦄ y = prop-ext ((λ _ → ↑prop ⋆ₚ) , ∨left)
∨-lift-⊤ {𝒰} = right-zero-of-commutative-left-zero (Lift𝒰ᵖ ⊤) (_∨_ {𝒰}{𝒰})

open import Structure.Monoid

Monoid∧ : Monoid (𝒰 ᵖ)
_∙_ ⦃ Monoid∧ ⦄ = _∧_
e ⦃ Monoid∧ ⦄ = Lift𝒰ᵖ ⊤

Monoid∨ : Monoid (𝒰 ᵖ)
_∙_ ⦃ Monoid∨ ⦄ = _∨_
e ⦃ Monoid∨ ⦄ = Lift𝒰ᵖ ⊥

open import Structure.Hemiring

instance
  FormHemiring-∨-∧-⊥ : FormHemiring _∨_ _∧_ ⊥
  FormHemiring-∨-∧-lift-⊥ : FormHemiring _∨_ _∧_ (Lift𝒰ᵖ {𝒱 = 𝒰} ⊥)

open import Proof
open import Logic.Proof

[+]*==*+* ⦃ FormHemiring-∨-∧-lift-⊥ ⦄ _ _ _ = prop-ext [∨]∧↔∧∨∧
*[+]==*+* ⦃ FormHemiring-∨-∧-lift-⊥ ⦄ a b c =
  proof a ∧ (b ∨ c)
    === (b ∨ c) ∧ a   :by: comm a (b ∨ c)
    === b ∧ a ∨ c ∧ a :by: prop-ext [∨]∧↔∧∨∧
    === a ∧ b ∨ a ∧ c :by: ap2 _∨_ (comm b a) (comm c a)
  qed
[+]*==*+* ⦃ FormHemiring-∨-∧-⊥ ⦄ = [+]*==*+* ⦃ FormHemiring-∨-∧-lift-⊥ ⦄
*[+]==*+* ⦃ FormHemiring-∨-∧-⊥ ⦄ = *[+]==*+* ⦃ FormHemiring-∨-∧-lift-⊥ ⦄

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

