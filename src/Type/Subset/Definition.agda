{-# OPTIONS --exact-split --safe #-}
module Type.Subset.Definition where

open import Universes

Subset : ∀ 𝒰 (X : 𝒱 ˙) → 𝒰 ⁺ ⊔ 𝒱 ˙
Subset 𝒰 X = X → 𝒰 ˙

open import Collection hiding (Subset) public

instance
  SubsetCollection : Collection 𝒰 (Subset 𝒰 X) X
  SubsetEmpty : Empty (Subset 𝒰 X) X
  SubsetUniversal : Universal (Subset 𝒰 X) X
  SubsetIntersection : Intersection (Subset 𝒰 X) X
  SubsetUnion : Union (Subset 𝒰 X) X
  SubsetInsertable : {X : 𝒰 ˙} → Insertable (Subset 𝒰 X) X
  SubsetRemovable : {X : 𝒰 ˙} → Removable (Subset 𝒰 X) X
  SubsetSubset : {X : 𝒰 ˙} → Collection.Subset 𝒰 (Subset 𝒰 X) X

_∈_ ⦃ SubsetCollection ⦄ x c = c x

open import Logic

∅ ⦃ SubsetEmpty ⦄ _ = Lift𝒰 ⊥
_∉∅ ⦃ SubsetEmpty ⦄ _ ()

Univ ⦃ SubsetUniversal ⦄ _ = Lift𝒰 ⊤
_∈Univ ⦃ SubsetUniversal ⦄ _ = ↑ ⋆

open import Type.Identity.Definition

_∩_ ⦃ SubsetIntersection ⦄ S₀ S₁ x = x ∈ S₀ ∧ x ∈ S₁
∩-valid ⦃ SubsetIntersection ⦄ {x}{S₀}{S₁} = ==→↔ (refl (x ∈ S₀ ∧ x ∈ S₁))

_∪_ ⦃ SubsetUnion ⦄ S₀ S₁ x = x ∈ S₀ ∨ x ∈ S₁
∪-valid ⦃ SubsetUnion ⦄ {x}{S₀}{S₁} = ==→↔ (refl (x ∈ S₀ ∨ x ∈ S₁))

insert ⦃ SubsetInsertable ⦄ x S x' = x' ∈ S ∨ x == x'
insert-valid ⦃ SubsetInsertable ⦄ {x}{y}{S} = ==→↔ (refl (y ∈ S ∨ x == y))

remove ⦃ SubsetRemovable ⦄ x S x' = x' ∈ S ∧ x' ≠ x
remove-valid ⦃ SubsetRemovable ⦄ {y}{x}{S} = ==→↔ (refl (y ∈ S ∧ y ≠ x))

Collection.Subset.collection SubsetSubset = SubsetCollection
_ᶜ ⦃ SubsetSubset ⦄ X x = x ∉ X
ᶜ-valid ⦃ SubsetSubset ⦄ {x}{X} = ==→↔ (refl (x ∉ X))

open import Type.Sum

SubsetType : {X : 𝒰 ˙}(S : Subset 𝒱 X) → 𝒰 ⊔ 𝒱 ˙ 
SubsetType {X = X} S = Σ λ (x : X) → x ∈ S
