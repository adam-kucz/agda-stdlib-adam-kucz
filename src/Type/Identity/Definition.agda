{-# OPTIONS --exact-split --safe #-}
module Type.Identity.Definition where

open import Universes

data Id (X : 𝒰 ˙) : (Y : 𝒰 ˙) (x : X) (y : Y) → 𝒰 ˙ where
  instance refl : (x : X) → Id X X x x

infix 19 _≡_
_≡_ : {X Y : 𝒰 ˙}
  (x : X)
  (y : Y)
  → -------------
  𝒰 ˙
x ≡ y = Id _ _ x y

ap : ∀ {x y}
  (f : (x : X) → A x)
  (p : x ≡ y)
  → ----------
  f x ≡ f y
ap f (refl x) = refl (f x)

transport :
  (p : X ≡ Y)
  (x : X)
  → ----------
  Y
transport (refl _) x = x
