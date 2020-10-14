{-# OPTIONS --exact-split --safe #-}
module Structure.Semigroup.Definition where

open import Universes
open import Operation.Binary using (ClosedOp; Associative)

FormSemigroup : {X : 𝒰 ˙} (_∙_ : ClosedOp X) → 𝒰 ˙
FormSemigroup = Associative

record Semigroup (X : 𝒰 ˙) : 𝒰 ˙ where
  infixl 130 _∙_
  field
    _∙_ : ClosedOp X
    ⦃ def ⦄ : FormSemigroup _∙_

open Semigroup ⦃ ... ⦄ public
