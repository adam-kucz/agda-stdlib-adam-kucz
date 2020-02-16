{-# OPTIONS --exact-split --safe --prop #-}
module Type.Subset.Definition where

open import PropUniverses

Subset : ∀ 𝒰 (X : 𝒱 ˙) → 𝒰 ⁺ ⊔ 𝒱 ˙
Subset 𝒰 X = X → 𝒰 ᵖ

open import Data.Collection public

instance
  SubsetCollection : Collection 𝒰 (Subset 𝒰 X) X
  SubsetEmpty : Empty (Subset 𝒰 X) X
  SubsetInsertable : {X : 𝒰 ˙} → Insertable (Subset 𝒰 X) X
  SubsetRemovable : {X : 𝒰 ˙} → Removable (Subset 𝒰 X) X

_∈_ ⦃ SubsetCollection ⦄ x c = c x

open import Logic

∅ ⦃ SubsetEmpty ⦄ _ = Lift𝒰ᵖ ⊥
_∉∅ ⦃ SubsetEmpty ⦄ _ ()

open import Proposition.Identity.Definition

insert ⦃ SubsetInsertable ⦄ x S x' = x' ∈ S ∨ x == x'
insert-valid ⦃ SubsetInsertable ⦄ {x}{y}{S} = ==→↔ (refl (S y ∨ x == y))

remove ⦃ SubsetRemovable ⦄ x S x' = x' ∈ S ∧ x' ≠ x
remove-valid ⦃ SubsetRemovable ⦄ {y}{x}{S} = ==→↔ (refl (S y ∧ y ≠ x))

Univ : (X : 𝒰 ˙) → Subset 𝒱 X
Univ X _ = Lift𝒰ᵖ ⊤

open import Proposition.Sum

SubsetType : {X : 𝒰 ˙}(S : Subset 𝒱 X) → 𝒰 ⊔ 𝒱 ˙ 
SubsetType {X = X} S = Σₚ λ (x : X) → x ∈ S
