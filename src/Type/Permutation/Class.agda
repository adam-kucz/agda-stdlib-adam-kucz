{-# OPTIONS --safe --exact-split  #-}
module Type.Permutation.Class where

open import Type.Permutation.Definition

open import Universes
open import Data.List.Definition
import Relation.Binary as Rel
open Rel hiding (_~_)
open Rel
  using (Reflexive-rtc; Transitive-rtc; InheritsSymmetric-rtc)
  public

instance
  SymmetricSwap : Symmetric (single-swap {X = X})

sym ⦃ SymmetricSwap ⦄ (swap x y l) = swap y x l
sym ⦃ SymmetricSwap ⦄ (step x p) = step x (sym p)
