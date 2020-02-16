{-# OPTIONS --exact-split --safe --prop #-}
module Structure.Ring where

open import Structure.Semiring
open import Structure.Hemiring
open import Structure.Monoid

open import PropUniverses
open import Operation.Binary
  renaming (ClosedOp to Op) hiding (Op)

record FormRing {X : 𝒰 ˙}(_+_ _*_ : Op X)(zero one : X)(-_ : X → X) : 𝒰 ᵖ
  where
  field
    ⦃ semiring ⦄ : FormSemiring _+_ _*_ zero one
    ⦃ inverse ⦄ : Inverse -_ _+_ ⦃ FormMonoid.unit monoid+ ⦄

record Ring {X : 𝒰 ˙} : 𝒰 ˙ where
  field
    _+_ _*_ : Op X
    zero one : X
    -_ : X → X
    ⦃ def ⦄ : FormRing _+_ _*_ zero one -_

open Ring ⦃ ... ⦄ public

instance
  DefaultRing : {plus times : Op X}{zero one : X}{neg : X → X}
    ⦃ _ : FormHemiring plus times zero ⦄
    ⦃ _ : one IsLeftUnitOf times ⦄
    ⦃ _ : one IsRightUnitOf times ⦄
    ⦃ _ : LeftInverse neg plus ⦃ FormMonoid.unit monoid+  ⦄ ⦄
    ⦃ _ : RightInverse neg plus ⦃ FormMonoid.unit monoid+ ⦄ ⦄
    → -------------------
    FormRing plus times zero one neg

DefaultRing = record {}
