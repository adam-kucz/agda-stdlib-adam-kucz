{-# OPTIONS --exact-split #-}
module Axiom.ExcludedMiddle where

open import Universes
open import Type.Decidable

postulate
  excluded-middle : (X : 𝒰 ˙) → Decidable X

open import Logic

dne : ¬ (¬ X) → X
dne {X = X} p with excluded-middle X
dne p | true q = q
dne {X = X} p | false ¬q = ⊥-recursion X (p ¬q)

open import Logic

classic-→ : (X → Y) ↔ ¬ X ∨ Y
⟶ (classic-→ {X = X}) p with excluded-middle X
⟶ classic-→ p | true q = ∨right (p q)
⟶ classic-→ p | false ¬q = ∨left ¬q
⟵ classic-→ (∨left ¬p) p = ⊥-recursion _ (¬p p)
⟵ classic-→ (∨right q) p = q


