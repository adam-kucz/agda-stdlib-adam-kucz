{-# OPTIONS --safe --exact-split --prop  #-}
module Proposition.Permutation.Property where

open import Proposition.Permutation.Definition as Perm
  hiding (refl; trans)

open import Universes
open import Data.List
open import Collection
open import Logic
open import Proof
open import Logic.Proof

∈-~ : ∀ (x : X){l l'}(p : l ~ l')
  → -------------------------
  x ∈ l ↔ x ∈ l'
∈-~ x p = go p , go $ sym p
  where go : ∀ {l l'}(p : l ~ l')(q : x ∈ l) → x ∈ l'
        go (Perm.refl l) q = q
        go (Perm.trans p q) q' = go q $ go p q'
        go (swap {l}{l'} x y p) (x∈x∷ (y ∷ t)) = x∈tail y (x∈x∷ l')
        go (swap {l}{l'} x y p) (x∈tail x (x∈x∷ t)) = x∈x∷ (x ∷ l')
        go (swap x y p) (x∈tail x (x∈tail y q)) =
          x∈tail y $ x∈tail x $ go p q
        go (step {l}{l'} x p) (x∈x∷ t) = x∈x∷ l'
        go (step x p) (x∈tail x' q) = x∈tail x' $ go p q
