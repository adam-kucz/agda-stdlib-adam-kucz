{-# OPTIONS --exact-split --prop #-}
module Prop'.Identity.Transport where

open import Prop'.Identity.Definition using (_==_; refl)

open import PropUniverses
open import Prop'.Identity.Property
open import Function.Proof

postulate
  transport : {X Y : 𝒰 ˙} (p : X == Y) (x : X) → Y
  transport-refl : {X : 𝒰 ˙} {x : X} → transport (refl X) x == x

transport-eval :
  (p : X == Y)
  (x : X)
  → -----------------------
  transport p x == x
transport-eval (refl X) x = transport-refl

transportₚ : (p : 𝑋 == 𝑌) (q : 𝑋) → 𝑌
transportₚ (refl 𝑋) q = q
