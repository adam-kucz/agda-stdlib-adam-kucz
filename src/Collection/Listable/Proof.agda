{-# OPTIONS --exact-split --prop --safe #-}
module Collection.Listable.Proof where

open import Collection.Listable.Definition
open import Collection.Listable.Property

open import Universes
open import Proof

module Comoposable~
    {Col : 𝒰 ˙}
    {Elem : 𝒱 ˙}
    ⦃ lst : Listable 𝒲 Col Elem ⦄
    where
  open MakeTransComposable _~_ public
