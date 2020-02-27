{-# OPTIONS --exact-split --prop --safe  #-}
module Logic.Proof where

open import Logic.Basic
open import Logic.Iff

open import PropUniverses
open import Relation.Binary.Property

instance
  Symmetric∨ : Symmetric (_∨_ {𝒰})

  Symmetric∧ : Symmetric (_∧_ {𝒰})
  Transitive∧ : Transitive (_∧_ {𝒰})

  Reflexive↔ : Reflexive (_↔_ {𝒰})
  Symmetric↔ : Symmetric (_↔_ {𝒰})
  Transitive↔ : Transitive (_↔_ {𝒰})

sym ⦃ Symmetric∨ ⦄ (∨left p) = ∨right p
sym ⦃ Symmetric∨ ⦄ (∨right q) = ∨left q

sym ⦃ Symmetric∧ ⦄ (left , right) = right , left
trans ⦃ Transitive∧ ⦄ (left , _) (_ , right) = left , right

refl ⦃ Reflexive↔ ⦄ x = (λ p → p) , (λ p → p)
sym ⦃ Symmetric↔ ⦄ (x→y , y→x) = y→x , x→y
trans ⦃ Transitive↔ ⦄ (x→y , y→x) (y→z , z→y) =
  (λ x → y→z (x→y x)) ,
  (λ z → y→x (z→y z))

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
