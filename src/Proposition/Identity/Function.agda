{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Function where

open import Proposition.Identity.Definition

open import PropUniverses
open import Function.Property

type== : {x : X} {y : Y}
  (p : x == y)
  → ----------
  X == Y
type== {X = X}(refl _) = refl X

subst :
  (𝐴 : (x : X) → 𝒰 ᵖ)
  {x y : X}
  (p : x == y)
  (ax : 𝐴 x)
  → ----------
  𝐴 y
subst 𝐴 (refl x) ax = ax

coe :
  (p : 𝑋 == 𝑌)
  (x : 𝑋)
  → ----------
  𝑌
coe (refl 𝑋) x = x

coe-eval :
  {𝑋 : 𝒰 ᵖ}
  (p : 𝑋 == 𝑌)
  (x : 𝑋)
  {A : {𝑋 : 𝒰 ᵖ}(x : 𝑋) → 𝒱 ˙}
  (f : {𝑋 : 𝒰 ᵖ}(x : 𝑋) → A x)
  → ---------------
  f (coe p x) == f x
coe-eval (refl _) x f = refl (f x)

-- more general than Function.Proof.ap
-- it doesn't require the two sides
-- to be of the same type
ap : {I : 𝒰 ˙}{F : I → 𝒱 ˙}{A : (i : I)(x : F i) → 𝒲 ˙}
  (inject : Injective F)
  (f : ∀ {i}(x : F i) → A i x)
  {i j : I}{x : F i}{y : F j}
  (p : x == y)
  → ----------
  f x == f y
ap inject f p with inj (type== p)
  where instance _ = inject
ap inject f (refl x) | refl i = refl (f x)

ap2 :
  {K : (x : X)(y : A x) → 𝒰 ˙}
  (f : (x : X)(y : A x) → K x y)
  {x x' : X}
  (p : x == x')
  {y : A x}{y' : A x'}
  (q : y == y')
  → ------------------------------
  f x y == f x' y'
ap2 f (refl x) (refl y) = refl (f x y)
