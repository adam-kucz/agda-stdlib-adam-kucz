{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity where

open import Proposition.Identity.Homogeneous public
module Het where
  open import Proposition.Identity.Heterogeneous public
module Id where
  open import Proposition.Identity.Function public
open import Proposition.Identity.Property public
open import Function.Proof using (ap) public

