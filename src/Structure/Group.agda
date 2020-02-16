{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Group where

open import Structure.Semigroup
open import Structure.Monoid

open import PropUniverses
open import Proposition.Identity using (_==_)
open import Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

record FormGroup {X : 𝒰 ˙} (_∙_ : Op X) (e : X) (_⁻¹ : (x : X) → X) : 𝒰 ᵖ where
  -- TODO: figure out why this has no effect
  -- infixl 160 _⁻¹
  -- infixl 130 _∙_
  field
    ⦃ form-monoid ⦄ : FormMonoid _∙_ e
    ⦃ inverse ⦄ : Inverse _⁻¹ _∙_ ⦃ FormMonoid.unit form-monoid ⦄

record Group (X : 𝒰 ˙) : 𝒰 ˙ where
  field
    _∙_ : Op X
    e : X
    _⁻¹ : (x : X) → X
    ⦃ def ⦄ : FormGroup _∙_ e _⁻¹

open Group ⦃ ... ⦄ public

-- lit name: canonical structures
instance
  -- TODO: find a way of using compound properties in default definitions
  DefaultGroup : {op : Op X} {e : X} {_⁻¹ : (x : X) → X}
    ⦃ _ : FormSemigroup op ⦄
    ⦃ _ : e IsLeftUnitOf op ⦄
    ⦃ _ : e IsRightUnitOf op ⦄
    ⦃ _ : LeftInverse _⁻¹ op ⦄
    ⦃ _ : RightInverse _⁻¹ op ⦄
    → -------------------
    FormGroup op e _⁻¹

DefaultGroup = record {}
  
