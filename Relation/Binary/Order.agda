{-# OPTIONS --exact-split --safe --prop #-}
open import PropUniverses renaming (_⊔_ to _⨿_)
open import Relation.Binary.Definition

module Relation.Binary.Order {X : 𝒰 ˙} (_⊑_ : Rel 𝒱 X X) where
  record Bottom (⊥ : X) : 𝒰 ⨿ 𝒱 ˙ where
    field
      bot : ∀ x → ⊥ ⊑ x

  open Bottom ⦃ ... ⦄ public

  
