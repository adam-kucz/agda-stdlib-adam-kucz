{-# OPTIONS --exact-split --prop  #-}
module Logic.Property where

open import Logic.Basic
open import Logic.Iff

open import PropUniverses
open import Relation.Binary.Property
open import Operation.Binary

instance
  Symmetric∨ : Symmetric (_∨_ {𝒰})
  Associative∨ : Associative (_∨_ {𝒰})
  Idempotent∨ : Idempotent (_∨_ {𝒰})

  Symmetric∧ : Symmetric (_∧_ {𝒰})
  Transitive∧ : Transitive (_∧_ {𝒰})
  Associative∧ : Associative (_∧_ {𝒰})
  Idempotent∧ : Idempotent (_∧_ {𝒰})

  Reflexive↔ : Reflexive (_↔_ {𝒰})
  Symmetric↔ : Symmetric (_↔_ {𝒰})
  Transitive↔ : Transitive (_↔_ {𝒰})

  Symmetric→Commutative :
    {logic-op : ClosedOp (𝒰 ᵖ)}
    ⦃ _ : Symmetric logic-op ⦄
    → --------------------------
    Commutative logic-op

open import Axiom.PropositionExtensionality

sym ⦃ Symmetric∨ ⦄ (∨left p) = ∨right p
sym ⦃ Symmetric∨ ⦄ (∨right q) = ∨left q
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
assoc ⦃ Associative∧ ⦄ x y z = prop-ext (
  (λ { (p , (q , r)) → p , q , r}) ,
  λ { (p , q , r) → p , (q , r)})
idemp ⦃ Idempotent∧ ⦄ x = prop-ext (∧left , λ q → q , q)

refl ⦃ Reflexive↔ ⦄ x = (λ p → p) , (λ p → p)
sym ⦃ Symmetric↔ ⦄ (x→y , y→x) = y→x , x→y
trans ⦃ Transitive↔ ⦄ (x→y , y→x) (y→z , z→y) =
  (λ x → y→z (x→y x)) ,
  (λ z → y→x (z→y z))

comm ⦃ Symmetric→Commutative ⦄ x y = prop-ext (sym , sym)

open import Proof

module WithUniverse {𝒰}{𝒱} where
  open MakeComposable (_↔_ {𝒰}{𝒱}) public
open WithUniverse public

instance
  StrongSymmetric↔ : StrongSymmetric {F = _ᵖ} _↔_
  composable-↔ : Composable (𝒰 ⊔ 𝒲) (_↔_ {𝒰}{𝒱}) (_↔_ {𝒱}{𝒲})

strong-sym ⦃ StrongSymmetric↔ ⦄ (x→y , y→x) = y→x , x→y

Composable.rel composable-↔ = _↔_
Composable.compose composable-↔ (x→y , y→x) (y→z , z→y) =
  (λ x → y→z (x→y x)) ,
  (λ z → y→x (z→y z))
