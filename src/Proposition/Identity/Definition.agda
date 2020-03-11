{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Definition where

-- set default Identity import to Homogeneous
open import Proposition.Identity.Homogeneous.Definition public
module Het where
  open import Proposition.Identity.Heterogeneous.Definition public
open import Proposition.Identity.Conversion public
