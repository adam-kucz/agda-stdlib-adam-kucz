{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.BasicProperty where

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

open import Proposition.Identity
open import Function hiding (_$_; _~_)

instance
  Injective-suc : Injective suc

inj ⦃ Injective-suc ⦄ (Het.refl (suc m)) = refl m

