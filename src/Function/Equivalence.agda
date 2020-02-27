{-# OPTIONS --exact-split --safe --prop #-}
module Function.Equivalence where

open import PropUniverses
open import Function.Basic
open import Proposition.Identity.Definition using (_==_; refl)

infix 19 _~_
_~_ : {X : 𝒰 ˙} {A B : (x : X) → 𝒱 ˙}
  (f : Π A) (g : Π B)
  → -----------------
  𝒰 ⊔ 𝒱 ᵖ
f ~ g = ∀ x → f x == g x

==→~ :
  {f g : Π A}
  (p : f == g)
  → -----------------
  f ~ g
==→~ (refl f) x = refl (f x)
