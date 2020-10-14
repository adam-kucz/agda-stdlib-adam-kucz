{-# OPTIONS --exact-split --safe #-}
module Operation.Binary.Lattice where

open import Operation.Binary.Definition
open import Operation.Binary.Property

open import Universes as Univ
open import Relation.Binary.Definition renaming (Rel to BinRel) using ()

record FormSemilattice {X : 𝒰 ˙}(_∙_ : ClosedOp X) : 𝒰 ˙ where
  field
    ⦃ semilattice-assoc ⦄ : Associative _∙_
    ⦃ semilattice-comm ⦄ : Commutative _∙_
    ⦃ semilattice-idemp ⦄ : Idempotent _∙_

open FormSemilattice ⦃ ... ⦄ public

instance
  DefaultSemilattice : {_∙_ : ClosedOp X}
    ⦃ _ : Associative _∙_ ⦄
    ⦃ _ : Commutative _∙_ ⦄
    ⦃ _ : Idempotent _∙_ ⦄
    → ----------------------------------
    FormSemilattice _∙_
DefaultSemilattice = record {}

record FormBoundedSemilattice {X : 𝒰 ˙}(_∙_ : ClosedOp X)(bound : X) : 𝒰 ˙ where
  field
    ⦃ semilattice ⦄ : FormSemilattice _∙_
    ⦃ bounded ⦄ : bound IsUnitOf _∙_

open FormBoundedSemilattice ⦃ ... ⦄ public

instance
  DefaultBoundedSemilattice : {_∙_ : ClosedOp X}{bound : X}
    ⦃ _ : Associative _∙_ ⦄
    ⦃ _ : Commutative _∙_ ⦄
    ⦃ _ : Idempotent _∙_ ⦄
    ⦃ _ : bound IsLeftUnitOf _∙_ ⦄
    ⦃ _ : bound IsRightUnitOf _∙_ ⦄
    → ----------------------------------
    FormBoundedSemilattice _∙_ bound
DefaultBoundedSemilattice = record {}
