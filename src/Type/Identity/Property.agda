{-# OPTIONS --exact-split --safe --prop #-}
module Type.Identity.Property where

open import Type.Identity.Definition

open import Universes
open import Proposition.Identity

≡→het== : {x : X} {y : Y}
  (id : x ≡ y)
  → ------------
  x Het.== y
≡→het== (refl x) = Het.refl x

trans : {x : X} {y : Y} {z : Z}
  (p : x ≡ y)
  (q : y ≡ z)
  → --------------
  x ≡ z
trans (refl _) q = q

transport== :
  (x : X)
  (p : X ≡ Y)
  → -----------------
  transport p x Het.== x
transport== x (refl _) = Het.refl x
