{-# OPTIONS --exact-split --prop #-}
module Type.Identity.ConversionAxiom where

open import Type.Identity.Definition

open import Universes
open import Prop'.Identity.Definition

postulate
  ==→≡ : {x : X} {y : Y}
    (p : x == y)
    → ------------
    x ≡ y

transport== : (p : X == Y) (x : X) → Y
transport== p x with ==→≡ p
transport== p x | refl X = x
