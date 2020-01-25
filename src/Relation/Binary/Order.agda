{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses renaming (_⊔_ to _⨿_)
open import Relation.Binary.Definition

module Relation.Binary.Order {X : 𝒰 ˙} (_⊑_ : Rel 𝒱 X X) where

record IsBottom (⊥ : X) : 𝒰 ⨿ 𝒱 ᵖ where
  field
    bot : ∀ x → ⊥ ⊑ x

open IsBottom ⦃ ... ⦄ public

open import Relation.Binary.Property

record FormPreorder : 𝒰 ⨿ 𝒱 ᵖ where
  field
    ⦃ reflexive ⦄ : Reflexive _⊑_
    ⦃ transitive ⦄ : Transitive _⊑_

instance
  DefaultPreorder :
    ⦃ _ : Reflexive _⊑_ ⦄
    ⦃ _ : Transitive _⊑_ ⦄
    → -------------------
    FormPreorder
DefaultPreorder = record {}

record FormPartialOrder : 𝒰 ⨿ 𝒱 ᵖ where
  field
    ⦃ preord ⦄ : FormPreorder
    ⦃ antisymmetric ⦄ : Antisymmetric _⊑_

instance
  DefaultPartialOrder :
    ⦃ _ : Reflexive _⊑_ ⦄
    ⦃ _ : Transitive _⊑_ ⦄
    ⦃ _ : Antisymmetric _⊑_ ⦄
    → -------------------
    FormPartialOrder
DefaultPartialOrder = record {}

record FormTotalOrder : 𝒰 ⨿ 𝒱 ᵖ where
  field
    ⦃ partial-order ⦄ : FormPartialOrder
    ⦃ total ⦄ : Connex _⊑_

instance
  DefaultTotalOrder :
    ⦃ _ : Reflexive _⊑_ ⦄
    ⦃ _ : Transitive _⊑_ ⦄
    ⦃ _ : Antisymmetric _⊑_ ⦄
    ⦃ _ : Connex _⊑_ ⦄
    → -------------------
    FormTotalOrder
DefaultTotalOrder = record {}

record FormAscendingChain (⊥ : X) : 𝒰 ⨿ 𝒱 ᵖ where
  field
    ⦃ bottom ⦄ : IsBottom ⊥
    ⦃ total-order ⦄ : FormTotalOrder 

instance
  DefaultAscendingChain :
    ⦃ _ : Reflexive _⊑_ ⦄
    ⦃ _ : Transitive _⊑_ ⦄
    ⦃ _ : Antisymmetric _⊑_ ⦄
    ⦃ _ : Connex _⊑_ ⦄
    {⊥ : X}
    ⦃ _ : IsBottom ⊥ ⦄
    → -------------------
    FormAscendingChain ⊥
DefaultAscendingChain = record {}

