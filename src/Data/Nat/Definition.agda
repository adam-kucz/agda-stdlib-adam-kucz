{-# OPTIONS --without-K --exact-split --safe #-}
module Data.Nat.Definition where

open import Universes

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

variable
  m n k l : ℕ

pred : (m : ℕ) → ℕ
pred zero    = zero
pred (suc m) = m
