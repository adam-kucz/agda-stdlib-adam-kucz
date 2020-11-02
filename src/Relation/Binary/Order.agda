{-# OPTIONS --exact-split --safe #-}
module Relation.Binary.Order where

open import Universes renaming (_⊔_ to _⨿_)
open import Relation.Binary.Definition

module WithOrder {X : 𝒰 ˙}(_⊑_ : BinRel 𝒱 X) where
  record IsBottom (⊥ : X) : 𝒰 ⨿ 𝒱 ˙ where
    field
      bot : ∀ x → ⊥ ⊑ x
  
  open IsBottom ⦃ ... ⦄ public
  
  open import Relation.Binary.Property
  
  record FormPreorder : 𝒰 ⨿ 𝒱 ˙ where
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
  
  record FormPartialOrder : 𝒰 ⨿ 𝒱 ˙ where
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
  
  record FormTotalOrder : 𝒰 ⨿ 𝒱 ˙ where
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
  
  record FormAscendingChain (⊥ : X) : 𝒰 ⨿ 𝒱 ˙ where
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
  
open WithOrder public

is-monotone : {X : 𝒰 ˙}{Y : 𝒱 ˙}
  (_⊑₀_ : BinRel 𝒲 X)
  (_⊑₁_ : BinRel 𝒳 Y)
  ⦃ preord : FormPreorder _⊑₀_ ⦄
  ⦃ preord : FormPreorder _⊑₁_ ⦄
  → --------------------------------------------------
  (f : X → Y) → 𝒰 ⨿ 𝒲 ⨿ 𝒳 ˙
is-monotone _⊑₀_ _⊑₁_ f = ∀{x₀ x₁}(p : x₀ ⊑₀ x₁) → f x₀ ⊑₁ f x₁ 
