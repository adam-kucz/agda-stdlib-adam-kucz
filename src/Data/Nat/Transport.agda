{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Transport where

open import Type.Identity
open import Proposition.Identity hiding (ap)
open import Data.Nat.Definition
open import Data.Nat.Arithmetic
open import Data.Nat.Property

open import Universes
open import Function.Property
open import Operation.Binary.Property

ℕ==→≡ : ∀ {m n : ℕ}
  (p : m == n)
  → --------------------
  m ≡ n
ℕ==→≡ {zero}{zero} p = refl zero
ℕ==→≡ {suc m}{suc n} p = ap suc (ℕ==→≡ (inj {f = suc} p))
