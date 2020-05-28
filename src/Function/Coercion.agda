{-# OPTIONS --exact-split --prop #-}
module Function.Coercion where

open import Function hiding (_$_)

open import Universes
open import Proof

open import Axiom.FunctionExtensionality
open import Proposition.Identity.Coercion

∘-coe :
  (p : X == Y)
  (f : (y : Y) → A y)
  → -------------------------
  f ∘ coe p Het.== f
∘-coe (Id-refl X) f = fun-ext λ x → ap f $ coe-eval (Id-refl X) x

coe-∘ :
  (f : Π A)
  (p : ∀ {x} → A x == B x)
  → -------------------------
  coe p ∘ f ~ f
coe-∘ f p x = coe-eval p (f x)

