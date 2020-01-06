{-# OPTIONS --exact-split --safe --prop #-}
module Structure.PartialOrder where

open import Structure.Preorder

open import PropUniverses
open import Relation.Binary

record FormPartialOrder {X : 𝒰 ˙} (_⊑_ : Rel 𝒱 X X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ preord ⦄ : FormPreorder _⊑_
    ⦃ antisymmetric ⦄ : Antisymmetric _⊑_

record PartialOrder 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    _⊑_ : Rel 𝒰 X X
    ⦃ def ⦄  : FormPartialOrder _⊑_

open Preorder ⦃ ... ⦄ public

instance
  DefaultPartialOrder : {R : Rel 𝒰 X X}
    ⦃ _ : Reflexive R ⦄
    ⦃ _ : Transitive R ⦄
    ⦃ _ : Antisymmetric R ⦄
    → -------------------
    FormPartialOrder R
  DefaultPartialOrder = record {}
  
