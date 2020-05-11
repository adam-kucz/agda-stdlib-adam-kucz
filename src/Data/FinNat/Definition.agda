{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinNat.Definition where

open import Universes
open import Data.Nat.Definition
open import Data.Nat.Syntax as N using (Nat)
open import Data.Nat.Order
open import Function using (_$_)

-- types of natural numbers less than index
data Finℕ : (n : ℕ) → 𝒰₀ ˙ where
  zero : ∀ {n} → Finℕ (suc n)
  suc : ∀ {n} → (x : Finℕ n) → Finℕ (suc n)

instance
  NatFinℕ : ∀ {n} → Nat 𝒰₀ (Finℕ n)
  Nat.Constraint (NatFinℕ {n}) m = m <ₜ n
  Nat.fromℕ (NatFinℕ {suc n}) zero = zero
  Nat.fromℕ (NatFinℕ {suc n}) (suc m) = suc $ Nat.fromℕ (NatFinℕ {n}) m

open import Logic using (⋆ₚ) public
open N using (fromℕ) public

toℕ : ∀ {n} → Finℕ n → ℕ
toℕ zero = 0
toℕ (suc x) = suc (toℕ x)

maxFinℕ : ∀ n → Finℕ (suc n)
maxFinℕ zero = zero
maxFinℕ (suc n) = suc (maxFinℕ n)

open import Function.Proof

toFinℕ : ∀ {m} n (n≤m : suc n ≤ m) → Finℕ m
toFinℕ {suc m} zero _ = zero
toFinℕ {suc m} (suc n) n<m = suc $ toFinℕ n (ap pred n<m)

module Pattern where
  pattern _+1 x = Finℕ.suc x
  pattern ₀ = Finℕ.zero
  pattern ₁ = ₀ +1
  pattern ₂ = ₁ +1 
  pattern ₃ = ₂ +1 
  pattern ₄ = ₃ +1 
  pattern ₅ = ₄ +1 
  pattern ₆ = ₅ +1 
  pattern ₇ = ₆ +1 
  pattern ₈ = ₇ +1 
  pattern ₉ = ₈ +1 
