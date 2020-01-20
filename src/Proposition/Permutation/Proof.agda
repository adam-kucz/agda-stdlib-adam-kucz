{-# OPTIONS --exact-split --prop --safe #-}
module Proposition.Permutation.Proof where

open import Proposition.Permutation.Definition
open import Proposition.Permutation.Multi
open import Proposition.Permutation.Inclusion

open import Universes
open import Proof
open import Proposition.Identity using (_==_)
open import Relation.Binary.Property using (subrel)

instance
  comp-~-== : {X : 𝒰 ˙} → Composable 𝒰 (_~_ {X = X}) _==_
  comp-~-== = composable-R-== _~_

  comp-==-~ : {X : 𝒰 ˙} → Composable 𝒰 _==_ (_~_ {X = X})
  comp-==-~ = composable-==-R _~_

  comp-~~-== : {X : 𝒰 ˙} → Composable 𝒰 (_~~_ {X = X}) _==_
  comp-~~-== = composable-R-== _~~_

  comp-==-~~ : {X : 𝒰 ˙} → Composable 𝒰 _==_ (_~~_ {X = X})
  comp-==-~~ = composable-==-R _~~_

  comp-~-~~ : {X : 𝒰 ˙} → Composable 𝒰 _~_ (_~~_ {X = X})
  Composable.rel comp-~-~~ = _~~_
  Composable.compose comp-~-~~ p q = trans (subrel p) q

  comp-~~-~ : {X : 𝒰 ˙} → Composable 𝒰 _~~_ (_~_ {X = X})
  Composable.rel comp-~~-~ = _~~_
  Composable.compose comp-~~-~ p q = trans p (subrel q)
