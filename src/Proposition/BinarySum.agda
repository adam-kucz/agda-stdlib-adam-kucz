{-# OPTIONS --without-K --exact-split --safe --prop #-}
module Proposition.BinarySum where

open import PropUniverses

infixl 15 _∨_
data _∨_ (𝑋 : 𝒰 ᵖ) (𝑌 : 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  left : (p : 𝑋) → 𝑋 ∨ 𝑌
  right : (q : 𝑌) → 𝑋 ∨ 𝑌

∨-contract : (p : 𝑋 ∨ 𝑋) → 𝑋
∨-contract (left p) = p
∨-contract (right q) = q

∨-recursion : {𝐴 : 𝑋 ∨ 𝑌 → 𝒰 ᵖ}
  (p : (x : 𝑋) → 𝐴 (left x))
  (q : (y : 𝑌) → 𝐴 (right y))
  (x∨y : 𝑋 ∨ 𝑌)
  → ------------------------------
  𝐴 x∨y
∨-recursion p q (left x) = p x
∨-recursion p q (right y) = q y
