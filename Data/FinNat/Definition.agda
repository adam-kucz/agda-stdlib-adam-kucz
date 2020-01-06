{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinNat.Definition where

open import Universes
open import Data.Nat.Definition
open import Data.Nat.Syntax as N
open import Data.Nat.Order
open import Function using (_$_)

-- types of natural numbers less than index
data Finℕ : (n : ℕ) → 𝒰₀ ˙ where
  zero : ∀ {n} → Finℕ (suc n)
  suc : ∀ {n} → (x : Finℕ n) → Finℕ (suc n)

instance
  NatFinℕ : ∀ {n} → Nat (Finℕ n)
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

toFinℕ : ∀ {m} n (n<m : n < m) → Finℕ m
toFinℕ {suc m} zero _ = zero
toFinℕ {suc m} (suc n) n<m = suc $ toFinℕ n (s<s→-<- n<m)

