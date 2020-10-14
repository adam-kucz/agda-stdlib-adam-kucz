{-# OPTIONS --exact-split --safe #-}
module Data.Maybe.Definition where

open import Universes

data Maybe (X : 𝒰 ˙) : 𝒰 ˙ where
  nothing : Maybe X
  just : (x : X) → Maybe X

from-maybe :
  (f : (x : X) → A (just x))
  (y : A nothing)
  (mx : Maybe X)
  → -------------------------
  A mx
from-maybe f y nothing = y
from-maybe f y (just x) = f x

from-maybe' :
  (f : (x : X) → Y)
  (y : Y)
  (mx : Maybe X)
  → -------------------------
  Y
from-maybe' f y nothing = y
from-maybe' f y (just x) = f x

partial : (X : 𝒰 ˙)(A : X → 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
partial X A = (x : X) → Maybe (A x)

_⇀_ : (X : 𝒰 ˙)(Y : 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
X ⇀ Y = X → Maybe Y

syntax partial X (λ x → A) = [ x ∶ X ]⇀ A

open import Type.Identity
open import Type.Empty

_∈dom_ _∉dom_ : {A : X → 𝒰 ˙}
  (x : X)(f : [ x ∶ X ]⇀ A x) → 𝒰 ˙
_∉dom_ {A = A} x f = f x == nothing {X = A x}
x ∈dom f = ¬ x ∉dom f

