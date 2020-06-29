{-# OPTIONS --exact-split --prop  #-}
module Logic.UnsafeProperty where

open import Logic.Basic
open import Logic.Iff

open import PropUniverses
open import Relation.Binary.Property
open import Operation.Binary

instance
  Associative∨ : Associative (_∨_ {𝒰})
  Idempotent∨ : Idempotent (_∨_ {𝒰})

  Associative∧ : Associative (_∧_ {𝒰})
  Idempotent∧ : Idempotent (_∧_ {𝒰})

  Symmetric→Commutative :
    {logic-op : ClosedOp (𝒰 ᵖ)}
    ⦃ _ : Symmetric logic-op ⦄
    → --------------------------
    Commutative logic-op

open import Axiom.PropositionExtensionality

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

assoc ⦃ Associative∧ ⦄ x y z = prop-ext (
  (λ { (p , (q , r)) → p , q , r}) ,
  λ { (p , q , r) → p , (q , r)})
idemp ⦃ Idempotent∧ ⦄ x = prop-ext (∧left , λ q → q , q)

comm ⦃ Symmetric→Commutative ⦄ x y = prop-ext (sym , sym)
