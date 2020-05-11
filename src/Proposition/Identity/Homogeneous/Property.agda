{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Homogeneous.Property where

open import Proposition.Identity.Homogeneous.Definition
  renaming (Idₚ to Id)

open import Universes
open import Relation.Binary.Property as Rel
open Rel using (Default-~) public
open import Function.Proof

instance
  EmptyIrreflexive : Irreflexive (empty-rel X X)
  EmptySymmetric : Symmetric (empty-rel X X)
  EmptyAsymmetric : Asymmetric (empty-rel X X)
  EmptyAntisymmetric : Antisymmetric (empty-rel X X)
  EmptyLeftQuasiReflexive : LeftQuasiReflexive (empty-rel X X)
  EmptyRightQuasiReflexive : RightQuasiReflexive (empty-rel X X)
  EmptyRelatingAll : ∀ {f : (x : X) → A x}
    → Relating f (empty-rel X X) (λ {x}{y} → empty-rel (A x) (A y))

irrefl ⦃ EmptyIrreflexive ⦄ _ ()
sym ⦃ EmptySymmetric ⦄ ()
asym ⦃ EmptyAsymmetric ⦄ ()
antisym ⦃ EmptyAntisymmetric ⦄ ()
left-quasirefl ⦃ EmptyLeftQuasiReflexive ⦄ ()
right-quasirefl ⦃ EmptyRightQuasiReflexive ⦄ ()
rel-preserv ⦃ EmptyRelatingAll ⦄ ()

open import Relation.Binary.ReflexiveTransitiveClosure

open import Logic

instance
  Id⊆rtc-empty : Id X ⊆ refl-trans-close (empty-rel X X)
  rtc-empty⊆Id : refl-trans-close (empty-rel X X) ⊆ Id X 

private
  equiv : ∀ {x y} → x == y ↔ refl-trans-close (empty-rel X X) x y

⟶ equiv (Id.refl x) = rfl x
⟵ equiv (rfl x) = Id.refl x

Id⊆rtc-empty = ↔-→-⊆ equiv
rtc-empty⊆Id = ↔-→-⊇ equiv

module TransferredProperties {X : 𝒰 ˙} where
  open import
    Relation.Binary.ReflexiveTransitiveClosure.Transfer
    (Id X)(empty-rel X X)⦃ Default-~ ⦄
    public
  instance
    SymmetricId = InheritsSymmetricR
    RelatingId = InheritsRelatingR

