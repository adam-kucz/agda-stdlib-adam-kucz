{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Semigroup where

open import PropUniverses
open import Operation.Binary using (ClosedOp; Associative)

FormSemigroup : {X : 𝒰 ˙} (_∙_ : ClosedOp X) → 𝒰 ᵖ
FormSemigroup = Associative

record Semigroup (X : 𝒰 ˙) : 𝒰 ˙ where
  infixl 130 _∙_
  field
    _∙_ : ClosedOp X
    ⦃ def ⦄ : FormSemigroup _∙_

open Semigroup ⦃ ... ⦄ public
