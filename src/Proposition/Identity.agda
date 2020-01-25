{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity where

open import Proposition.Identity.Definition public
open import Proposition.Identity.Property public
module Id where
  open import Proposition.Identity.Function public
open import Function.Proof
  using (ap; Relating-all-==; ap'; RRelating-all-==) public

