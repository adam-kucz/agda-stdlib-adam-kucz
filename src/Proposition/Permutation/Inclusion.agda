{-# OPTIONS --safe --exact-split --prop  #-}
module Proposition.Permutation.Inclusion where

open import PropUniverses
open import Data.List
open import Relation.Binary
  renaming (refl to refl'; trans to trans')
  hiding (_~_)

open import Proposition.Permutation.Definition
open import Proposition.Permutation.Multi

private
  variable
    l l₁ l₂ l₃ : List X

instance
  ~⊆~~ : _⊆_ (_~_ {X = X}) _~~_ 
subrel ⦃ ~⊆~~ ⦄ (refl l) = refl l
subrel ⦃ ~⊆~~ ⦄ (trans p q) = trans (subrel p) (subrel q) 
subrel ⦃ ~⊆~~ ⦄ (swap x y p) = swap x y (subrel p)
subrel ⦃ ~⊆~~ ⦄ (step x p) = step x (subrel p)
