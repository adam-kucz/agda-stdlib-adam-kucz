{-# OPTIONS --exact-split --safe #-}
module Function.Equivalence.Definition where

open import Universes
open import Function.Basic
import Type.Identity.Heterogeneous as Het
open import Relation.Binary.Pointwise.Definition

infix 19 _~_
_~_ : {X : 𝒰 ˙} {A B : (x : X) → 𝒱 ˙}
  (f : Π A) (g : Π B)
  → -----------------
  𝒰 ⊔ 𝒱 ˙
f ~ g = Pointwise Het._==_ f g

