{-# OPTIONS --exact-split --safe --prop #-}
module Data.Bool.Property where

open import Data.Bool.Definition

open import PropUniverses
open import Proposition.Decidable

to-bool :
  (𝑋 : 𝒰 ᵖ)
  ⦃ _ : Decidable 𝑋 ⦄
  → ------------------
  Bool
to-bool 𝑋 with decide 𝑋
to-bool _ | true _ = true
to-bool _ | false _ = true

open import Proposition.Identity
open import Operation.Binary

instance
  and-assoc : Associative _and_
  assoc ⦃ and-assoc ⦄ true y z = refl (y and z)
  assoc ⦃ and-assoc ⦄ false _ _ = refl false

  or-assoc : Associative _or_
  assoc ⦃ or-assoc ⦄ true _ _ = refl true
  assoc ⦃ or-assoc ⦄ false y z = refl (y or z)

  and-comm : Commutative _and_
  comm ⦃ and-comm ⦄ true true = refl true
  comm ⦃ and-comm ⦄ true false = refl false
  comm ⦃ and-comm ⦄ false true = refl false
  comm ⦃ and-comm ⦄ false false = refl false

  or-comm : Commutative _or_
  comm ⦃ or-comm ⦄ true true = refl true
  comm ⦃ or-comm ⦄ true false = refl true
  comm ⦃ or-comm ⦄ false true = refl true
  comm ⦃ or-comm ⦄ false false = refl false

  true-and : true IsLeftUnitOf _and_
  left-unit ⦃ true-and ⦄ = refl

  false-or : false IsLeftUnitOf _or_
  left-unit ⦃ false-or ⦄ = refl
  
  and-true = right-unit-of-commutative-left-unit true _and_
  or-false = right-unit-of-commutative-left-unit false _or_

open import Structure.Monoid

MonoidAnd : Monoid Bool
_∙_ ⦃ MonoidAnd ⦄ = _and_
e ⦃ MonoidAnd ⦄ = true

MonoidOr : Monoid Bool
_∙_ ⦃ MonoidOr ⦄ = _or_
e ⦃ MonoidOr ⦄ = false
