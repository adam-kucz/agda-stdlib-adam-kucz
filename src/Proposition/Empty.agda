{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Proposition.Empty where

open import PropUniverses

data ⊥ : 𝒰₀ ᵖ where

⊥-induction : (A : (p : ⊥) → 𝒰 ˙) (p : ⊥) → A p
⊥-induction _ ()

⊥-recursion : (X : 𝒰 ˙) (p : ⊥) → X
⊥-recursion _ ()

⊥-inductionₚ : (𝐴 : (p : ⊥) → 𝒰 ᵖ) (p : ⊥) → 𝐴 p
⊥-inductionₚ _ ()

⊥-recursionₚ : (𝑋 : 𝒰 ᵖ) (p : ⊥) → 𝑋
⊥-recursionₚ _ ()

infix 18 ¬_ 
¬_ : (𝑋 : 𝒰 ᵖ) → 𝒰 ᵖ
¬ X = X → ⊥

empty : (X : 𝒰 ˙) → 𝒰 ᵖ
empty X = X → ⊥
