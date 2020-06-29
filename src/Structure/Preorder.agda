{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Preorder where

open import PropUniverses
open import Relation.Binary
open import Function.Proof using (Relating)

record Preorder 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    _⊑_ : Rel 𝒰 X X
    ⦃ def ⦄  : FormPreorder _⊑_

open Preorder ⦃ ... ⦄ public

monotone : {X : 𝒰 ˙}
  (_⊑₀_ : Rel 𝒱 X X)
  (_⊑₁_ : Rel 𝒲 Y Y)
  ⦃ P : FormPreorder _⊑₀_ ⦄
  ⦃ R : FormPreorder _⊑₁_ ⦄
  (f : (x : X) → Y)
  → -------------------
  𝒰 ⊔ 𝒱 ⊔ 𝒲 ᵖ
monotone _⊑₀_ _⊑₁_ f = Relating f _⊑₀_ _⊑₁_

module Composable⊑ (P : Preorder 𝒰 X) where
  open import Proof

  private instance _ = P
  open MakeTransComposable _⊑_ ⦃ FormPreorder.transitive def ⦄ public
