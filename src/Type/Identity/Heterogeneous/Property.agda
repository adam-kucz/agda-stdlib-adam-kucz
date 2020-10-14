{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Heterogeneous.Property where

open import Type.Identity.Heterogeneous.Definition

open import Universes
open import Relation.Binary.Property as Rel hiding (refl) 

instance
  Reflexive== : Reflexive (_==_ {X = X}{Y = X})
  Symmetric== : Symmetric (_==_ {X = X}{Y = X})

Rel.refl ⦃ Reflexive== ⦄ x = refl x
sym ⦃ Symmetric== ⦄ (refl x) = refl x
