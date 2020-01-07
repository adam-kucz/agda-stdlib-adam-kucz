{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Preorder where

open import PropUniverses
open import Relation.Binary
open import Function.Proof using (Relating)

record FormPreorder {X : 𝒰 ˙} (_⊑_ : Rel 𝒱 X X) : 𝒰 ⊔ 𝒱 ᵖ where
  field
    ⦃ reflexive ⦄ : Reflexive _⊑_
    ⦃ transitive ⦄ : Transitive _⊑_

record Preorder 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    _⊑_ : Rel 𝒰 X X
    ⦃ def ⦄  : FormPreorder _⊑_

open Preorder ⦃ ... ⦄ public

monotone : {X : 𝒰 ˙}
  ⦃ P : Preorder 𝒱 X ⦄
  ⦃ R : Preorder 𝒲 Y ⦄
  (f : (x : X) → Y)
  → -------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ᵖ
monotone f = Relating f _⊑_ _⊑_

instance
  DefaultPreorder : {R : Rel 𝒰 X X}
    ⦃ _ : Reflexive R ⦄
    ⦃ _ : Transitive R ⦄
    → -------------------
    FormPreorder R
  DefaultPreorder = record {}
  
