{-# OPTIONS --exact-split --safe --prop #-}
module Type.Equivalence where

open import PropUniverses
open import Prop'.Identity using (_==_; refl)
open import Logic using (∃; _,_)
open import Function using (id; Bijective)

_~_ : (X : 𝒰 ˙) (Y : 𝒱 ˙) → 𝒰 ⊔ 𝒱 ᵖ
X ~ Y = ∃ λ (f : X → Y) → Bijective f

equal-types-are-equivalent : (p : X == Y) → X ~ Y
equal-types-are-equivalent (refl X) = id , record {}


