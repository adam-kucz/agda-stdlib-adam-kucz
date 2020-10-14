{-# OPTIONS --exact-split --safe #-}
module Data.Nat.BasicProperty where

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

open import Type.Identity
open import Function hiding (_$_; _~_)

instance
  Injective-suc : Injective suc

inj ⦃ Injective-suc ⦄ (Het.refl (suc m)) = refl m

