{-# OPTIONS --exact-split --safe --prop #-}
module Structure.JoinSemilattice where

open import PropUniverses
open import Relation.Binary
open import Operation.Binary

record JoinSemilattice 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    _⊑_ : Rel 𝒰 X X
    _⊓_ : ClosedOp X
    ⦃ def ⦄  : FormJoinSemilattice _⊓_ _⊑_

open JoinSemilattice ⦃ … ⦄ public
