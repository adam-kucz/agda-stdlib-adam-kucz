{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Property where

open import Proposition.Identity.Homogeneous hiding (refl)
import Proposition.Identity.Heterogeneous as Het

open import Universes
open import Relation.Binary.Property

instance
  hom⊆het : (_==_ {X = X}) ⊆ Het._==_
  het⊆hom : Het._==_ ⊆ (_==_ {X = X})

subrel⊆ hom⊆het (Idₚ.refl x) = Het.refl x
subrel⊆ het⊆hom (Het.refl x) = Idₚ.refl x

