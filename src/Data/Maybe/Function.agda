{-# OPTIONS --exact-split --prop --safe #-}
module Data.Maybe.Function where

open import Data.Maybe.Definition

open import PropUniverses
open import Proposition.Unit

dmap : {𝐴 : Maybe X → 𝒰 ᵖ}
  (f : (x : X)(p : 𝐴 (just x)) → Y)
  → ----------------------------------------------
  (mx : Maybe X)(p : 𝐴 mx) → Maybe Y
dmap f nothing p = nothing
dmap f (just x) p = just (f x p)
