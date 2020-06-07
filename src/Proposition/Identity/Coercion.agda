{-# OPTIONS --exact-split --prop #-}
module Proposition.Identity.Coercion where

open import Proposition.Identity
open import Axiom.UniqueChoice

open import PropUniverses
open import Logic
open import Proposition.Sum
open import Relation.Binary

private
  uniq : (p : X == Y)(x : X) → ∃! λ (y : Y) → y Het.== x
uniq (refl X) x = x , (Het.refl x , λ _ p → subrel p)

coe : (p : X == Y) (x : X) → Y
coe p x = elem (!choice (uniq p x))

coe-eval :
  (p : X == Y)
  (x : X)
  → -------------------------
  coe p x Het.== x
coe-eval p x = ∧left (prop (!choice (uniq p x)))

coe-eval-hom :
  ⦃ p : X == X ⦄
  (x : X)
  → -------------------------
  coe p x == x
coe-eval-hom ⦃ p ⦄ x = subrel (coe-eval p x)

open import Proof

coe-2-eval :
  (p : Y == X)
  (q : X == Y)
  (x : X)
  → -------------------------
  coe p (coe q x) == x
coe-2-eval (Id.refl _)(Id.refl _) x =
  proof coe (Id.refl _) (coe (Id.refl _) x)
    === coe (Id.refl _) x :by: coe-eval-hom (coe (Id.refl _) x)
    === x                 :by: coe-eval-hom x
  qed

