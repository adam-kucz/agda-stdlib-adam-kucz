{-# OPTIONS --exact-split --prop --safe #-}
module Proposition.Permutation.Proof where

open import Proposition.Permutation.Definition
open import Proposition.Permutation.Multi

open import Universes
open import Proof
open import Proposition.Identity using (_==_)

instance
  comp-~-== : {X : 𝒰 ˙} → Composable 𝒰 (_~_ {X = X}) _==_
  comp-~-== = composable-R-== _~_

  comp-==-~ : {X : 𝒰 ˙} → Composable 𝒰 _==_ (_~_ {X = X})
  comp-==-~ = composable-==-R _~_

  comp-~~-== : {X : 𝒰 ˙} → Composable 𝒰 (_~~_ {X = X}) _==_
  comp-~~-== = composable-R-== _~~_

  comp-==-~~ : {X : 𝒰 ˙} → Composable 𝒰 _==_ (_~~_ {X = X})
  comp-==-~~ = composable-==-R _~~_
