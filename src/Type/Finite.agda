{-# OPTIONS --exact-split --exact-split --safe --prop #-}
module Type.Finite where

open import PropUniverses
open import Data.Vec
open import Logic

is-finite : (X : 𝒰 ˙) → 𝒰 ᵖ
is-finite X =
  ∃ λ n →
  ∃ λ (l : Vec X n) →
  ∀ x →
  x ∈ l

open import Proposition.Sum

Finite : (𝒰 : Universe) → 𝒰 ⁺ ˙
Finite 𝒰 = Σₚ λ (X : 𝒰 ˙) → is-finite X
