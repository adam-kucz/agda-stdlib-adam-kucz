{-# OPTIONS --exact-split --prop --safe #-}
module Proposition.Permutation.Proof where

open import Proposition.Permutation.Definition
open import Proposition.Permutation.Multi
open import Proposition.Permutation.Inclusion

open import Universes
open import Proof
open import Proposition.Identity using (_==_)
open import Relation.Binary.Property using (subrel)

module comp-~ {X : 𝒰 ˙} where
  open TransMakeComposable (_~_ {X = X}) public
module comp-~~ {X : 𝒰 ˙} where
  open TransMakeComposable (_~~_ {X = X}) public

instance
  comp-~-~~ : {X : 𝒰 ˙} → Composable 𝒰 _~_ (_~~_ {X = X})
  Composable.rel comp-~-~~ = _~~_
  Composable.compose comp-~-~~ p q = trans (subrel p) q

  comp-~~-~ : {X : 𝒰 ˙} → Composable 𝒰 _~~_ (_~_ {X = X})
  Composable.rel comp-~~-~ = _~~_
  Composable.compose comp-~~-~ p q = trans p (subrel q)
