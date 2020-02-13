{-# OPTIONS --exact-split --prop  #-}
module Logic.Property where

open import Logic.Basic
open import Logic.Iff

open import Universes
open import Relation.Binary.Property
open import Operation.Binary

instance
  Symmetric∨ : Symmetric (_∨_ {𝒰})
  Commutative∨ : Commutative (_∨_ {𝒰})
  Associative∨ : Associative (_∨_ {𝒰})
  Idempotent∨ : Idempotent (_∨_ {𝒰})

  Symmetric∧ : Symmetric (_∧_ {𝒰})
  Transitive∧ : Transitive (_∧_ {𝒰})
  Commutative∧ : Commutative (_∧_ {𝒰})
  Associative∧ : Associative (_∧_ {𝒰})
  Idempotent∧ : Idempotent (_∧_ {𝒰})

open import Axiom.PropositionExtensionality

sym ⦃ Symmetric∨ ⦄ (∨left p) = ∨right p
sym ⦃ Symmetric∨ ⦄ (∨right q) = ∨left q
comm ⦃ Commutative∨ ⦄ x y = prop-ext (sym , sym)
assoc ⦃ Associative∨ ⦄ x y z = prop-ext (
  (λ { (∨left p) → ∨left (∨left p)
     ; (∨right (∨left p)) → ∨left (∨right p)
     ; (∨right (∨right q)) → ∨right q}) ,
  λ { (∨left (∨left p)) → ∨left p
     ; (∨left (∨right p)) → ∨right (∨left p)
     ; (∨right q) → ∨right (∨right q)})
idemp ⦃ Idempotent∨ ⦄ x = prop-ext (
  (λ { (∨left p) → p
     ; (∨right q) → q}) ,
  λ q → ∨left q)

sym ⦃ Symmetric∧ ⦄ (left , right) = right , left
trans ⦃ Transitive∧ ⦄ (left , _) (_ , right) = left , right
comm ⦃ Commutative∧ ⦄ x y = prop-ext (sym , sym)
assoc ⦃ Associative∧ ⦄ x y z = prop-ext (
  (λ { (p , (q , r)) → p , q , r}) ,
  λ { (p , q , r) → p , (q , r)})
idemp ⦃ Idempotent∧ ⦄ x = prop-ext (∧left , λ q → q , q)

