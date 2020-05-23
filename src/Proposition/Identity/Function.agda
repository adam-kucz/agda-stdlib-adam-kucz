{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Identity.Function where

open import Proposition.Identity.Definition

open import PropUniverses
open import Function.Property

type== : {x : X} {y : Y}
  (p : x Het.== y)
  → ----------
  X == Y
type== {X = X}(Het.refl _) = Idₚ.refl X

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
  f (coe p x) Het.== f x
coe-eval (refl _) x f = Het.refl (f x)

-- more general than Function.Proof.ap
-- it doesn't require the two sides
-- to be of the same type
ap : {I : 𝒰 ˙}{F : I → 𝒱 ˙}{A : (i : I)(x : F i) → 𝒲 ˙}
  (inject : Injective F)
  (f : ∀ {i}(x : F i) → A i x)
  {i j : I}{x : F i}{y : F j}
  (p : x Het.== y)
  → ----------
  f x Het.== f y
ap inject f p with inj (==→het== (type== p))
  where instance _ = inject
ap inject f (Het.refl x) | refl i = Het.refl (f x)

ap2 :
  {K : (x : X)(y : A x) → 𝒰 ˙}
  (f : (x : X)(y : A x) → K x y)
  {x x' : X}
  (p : x == x')
  {y : A x}{y' : A x'}
  (q : y Het.== y')
  → ------------------------------
  f x y Het.== f x' y'
ap2 f (refl x) (Het.refl y) = Het.refl (f x y)

het-ap2 :
  {K : (x : X)(y : A x) → 𝒰 ˙}
  (f : (x : X)(y : A x) → K x y)
  {x x' : X}
  (p : x Het.== x')
  {y : A x}{y' : A x'}
  (q : y Het.== y')
  → ------------------------------
  f x y Het.== f x' y'
het-ap2 f (Het.refl x)(Het.refl y) = Het.refl (f x y)

het-ap3 :
  {K : (x : X)(y : A x) → 𝒰 ˙}
  {M : (x : X)(y : A x)(z : K x y) → 𝒱 ˙}
  (f : (x : X)(y : A x)(z : K x y) → M x y z)
  {x x' : X}
  (p : x == x')
  {y : A x}{y' : A x'}
  (q : y Het.== y')
  {z : K x y}{z' : K x' y'}
  (r : z Het.== z')
  → ------------------------------
  f x y z Het.== f x' y' z'
het-ap3 f (refl x)(Het.refl y)(Het.refl z) = Het.refl (f x y z)
