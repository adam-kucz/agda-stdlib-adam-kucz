{-# OPTIONS --exact-split --safe --prop #-}
module Structure.PartialOrder where

import Structure.Preorder as Pre

open import PropUniverses
open import Relation.Binary

record PartialOrder 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    _⊑_ : Rel 𝒰 X X
    ⦃ def ⦄  : FormPartialOrder _⊑_

open PartialOrder ⦃ … ⦄ public

module Composable⊑ (P : PartialOrder 𝒰 X) where
  private instance _ = P
  open Pre.Composable⊑ (record { _⊑_ = _⊑_ }) public
