{-# OPTIONS --safe --exact-split --prop  #-}
open import PropUniverses

module Data.List.Insertable {𝒰 : Universe} where

open import Data.List.Definition {𝒰}
open import Data.List.Collection {𝒰}

open import Collection.Insertable public
open import Proposition.Identity hiding (refl)
open import Proof
open import Logic

instance
  ListInsertable : Insertable (List X) X

insert ⦃ ListInsertable ⦄ = _∷_
⟶ (insert-valid ⦃ ListInsertable ⦄ {x = x}) (x∈x∷ _) = ∨right (refl x)
⟶ (insert-valid ⦃ ListInsertable ⦄) (x∈tail _ p) = ∨left p
⟵ (insert-valid ⦃ ListInsertable ⦄ {x = x}) (∨left p) = x∈tail x p
⟵ (insert-valid ⦃ ListInsertable ⦄) (∨right (Id.refl x)) = x∈x∷ _
