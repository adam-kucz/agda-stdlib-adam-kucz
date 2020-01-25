{-# OPTIONS --exact-split --safe --prop #-}
module Structure.AscendingChain where

open import PropUniverses
open import Relation.Binary

record AscendingChain 𝒰 (X : 𝒱 ˙) : 𝒰 ⁺ ⊔ 𝒱 ˙ where
  field
    _⊑_ : Rel 𝒰 X X
    ⊥ : X
    ⦃ def ⦄  : FormAscendingChain _⊑_ ⊥

open AscendingChain ⦃ … ⦄ public
