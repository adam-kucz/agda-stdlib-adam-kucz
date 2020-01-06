{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Monoid where

open import Structure.Semigroup

open import PropUniverses
open import Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

record FormMonoid {X : 𝒰 ˙} (_∙_ : Op X) (e : X) : 𝒰 ᵖ where
  field
    ⦃ form-semigroup ⦄ : FormSemigroup _∙_
    ⦃ unit ⦄ : e IsUnitOf _∙_

record Monoid (X : 𝒰 ˙) : 𝒰 ˙ where
  field
    _∙_ : Op X
    e : X
    ⦃ def ⦄  : FormMonoid _∙_ e

open Monoid ⦃ ... ⦄ public

instance
  DefaultMonoid : {op : Op X} {e : X}
    ⦃ _ : FormSemigroup op ⦄
    ⦃ _ : e IsLeftUnitOf op ⦄
    ⦃ _ : e IsRightUnitOf op ⦄
    → -------------------
    FormMonoid op e
  DefaultMonoid = record {}
  
