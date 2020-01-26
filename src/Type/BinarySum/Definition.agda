{-# OPTIONS --exact-split --safe --prop #-}
module Type.BinarySum.Definition where

open import Universes

infixl 55 _+_
data _+_ (X : 𝒰 ˙) (Y : 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  inl : (x : X) → X + Y
  inr : (y : Y) → X + Y

[_,_] :
  (f : (x : X) → Z)
  (g : (y : Y) → Z)
  → -----------------------
  (xy : X + Y) → Z
[ f , _ ] (inl x) = f x
[ _ , g ] (inr y) = g y

open import Function.Basic

[_+_] : {X' : 𝒰 ˙}{Y' : 𝒱 ˙}
  (f : (x : X) → X')
  (g : (y : Y) → Y')
  → -----------------------
  (xy : X + Y) → X' + Y'
[ f + g ] = [ inl ∘ f , inr ∘ g ]
