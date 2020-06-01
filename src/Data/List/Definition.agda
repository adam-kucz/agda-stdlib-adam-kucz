{-# OPTIONS --safe --exact-split --prop  #-}
open import PropUniverses

module Data.List.Definition {𝒰 : Universe} where

infixr 115 _∷_
data List (X : 𝒰 ˙) : 𝒰 ˙ where
  []  : List X
  _∷_ : (h : X) (t : List X) → List X

open import Data.Nat.Definition using (ℕ; zero; suc)
open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Order

open import Proposition.Identity
open import Proposition.Empty

last : (l : List X)(p : l ≠ []) → X
last {X = X} [] p = ⊥-recursion X (p (refl []))
last (x ∷ []) p = x
last (_ ∷ h ∷ l) p = last (h ∷ l) λ ()

pattern [_] a₀ = a₀ ∷ []
pattern [_⸴_] a₀ a₁ = a₀ ∷ a₁ ∷ []
pattern [_⸴_⸴_] a₀ a₁ a₂ = a₀ ∷ a₁ ∷ a₂ ∷ []
pattern [_⸴_⸴_⸴_] a₀ a₁ a₂ a₃ = a₀ ∷ a₁ ∷ a₂ ∷ a₃ ∷ []


