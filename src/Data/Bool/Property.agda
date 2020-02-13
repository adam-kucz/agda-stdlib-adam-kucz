{-# OPTIONS --exact-split --prop --safe #-}
module Data.Bool.Property where

open import Data.Bool.Definition

open import Proposition.Identity
open import Proposition.Decidable as Dec
  hiding (true; false)

instance
  DecidableBool== : {b₀ b₁ : Bool} → Decidable (b₀ == b₁)
DecidableBool== {true} {true} = Dec.true (refl true)
DecidableBool== {true} {false} = Dec.false λ ()
DecidableBool== {false} {true} = Dec.false λ ()
DecidableBool== {false} {false} = Dec.true (refl false)
