{-# OPTIONS --exact-split --safe #-}
module Data.Maybe.Function where

open import Data.Maybe.Definition

open import Universes
open import Type.Unit

dmap : {A : Maybe X → 𝒰 ˙}
  (f : (x : X)(p : A (just x)) → Y)
  → ----------------------------------------------
  (mx : Maybe X)(p : A mx) → Maybe Y
dmap f nothing p = nothing
dmap f (just x) p = just (f x p)
