{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Property where

open import Type.Identity.Homogeneous.Definition hiding (refl)
import Type.Identity.Heterogeneous as Het

open import Universes
open import Relation.Binary.Property

instance
  hom⊆het : (_==_ {X = X}) ⊆ Het._==_
  het⊆hom : Het._==_ ⊆ (_==_ {X = X})

subrel⊆ hom⊆het (Id.refl x) = Het.refl x
subrel⊆ het⊆hom (Het.refl x) = Id.refl x

