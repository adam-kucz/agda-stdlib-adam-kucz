{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity where

open import Proposition.Identity.Homogeneous public
module Id where
  open import Proposition.Identity.Function
    hiding (ap; het-ap2; type==) public
module Het where
  open import Proposition.Identity.Heterogeneous public
  open import Proposition.Identity.Function
    using (ap; type==) renaming (het-ap2 to ap2) public
open import Proposition.Identity.Property public
open import Function.Proof using (ap) public

