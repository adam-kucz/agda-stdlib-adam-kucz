{-# OPTIONS --exact-split --prop #-}
module Proposition.Identity.Coercion where

open import Proposition.Identity.Definition using (_==_; refl)
open import Axiom.UniqueChoice

open import PropUniverses
open import Logic
open import Proposition.Sum

private
  uniq : (p : X == Y)(x : X) → ∃! λ (y : Y) → y == x
  uniq (refl X) x = x , (refl x , λ _ p → p)

coe : (p : X == Y) (x : X) → Y
coe p x = elem (!choice (uniq p x))

coe-eval :
  (p : X == Y)
  (x : X)
  → -------------------------
  coe p x == x
coe-eval p x = ∧left (prop (!choice (uniq p x)))
