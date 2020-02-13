{-# OPTIONS --exact-split --prop #-}
module Axiom.ExcludedMiddle where

open import PropUniverses
open import Proposition.Decidable

postulate
  excluded-middle : (𝑋 : 𝒰 ᵖ) → Decidable 𝑋

open import Logic

dne : ¬ (¬ 𝑋) → 𝑋
dne {𝑋 = 𝑋} p with excluded-middle 𝑋
dne p | true q = q
dne {𝑋 = 𝑋} p | false ¬q = ⊥-recursion 𝑋 (p ¬q)

open import Logic

classic-→ : (𝑋 → 𝑌) ↔ ¬ 𝑋 ∨ 𝑌
⟶ (classic-→ {𝑋 = 𝑋}) p with excluded-middle 𝑋
⟶ classic-→ p | true q = ∨right (p q)
⟶ classic-→ p | false ¬q = ∨left ¬q
⟵ classic-→ (∨left ¬p) p = ⊥-recursion _ (¬p p)
⟵ classic-→ (∨right q) p = q
