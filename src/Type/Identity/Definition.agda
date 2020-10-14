{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Definition where

-- set default Identity import to Homogeneous
open import Type.Identity.Homogeneous.Definition public
module Het where
  open import Type.Identity.Heterogeneous.Definition public
open import Type.Identity.Conversion public
