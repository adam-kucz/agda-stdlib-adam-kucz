{-# OPTIONS --exact-split --safe #-}
module Relation.Binary.Pointwise.Definition where

open import Relation.Binary.Definition

open import Universes
open import Function.Basic

Pointwise : {X : 𝒰 ˙}{A : X → 𝒱 ˙}{B : X → 𝒲 ˙}
  (R : ∀ {x x'} → Rel 𝒳 (A x) (B x'))
  → ---------------------------------------------
  Rel (𝒰 ⊔ 𝒳) (Π A) (Π B)
Pointwise R f g = ∀ x → R (f x) (g x)
