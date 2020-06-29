{-# OPTIONS --exact-split --prop #-}
module Data.Nat.Operation where

open import Structure.Monoid
open import Data.Nat.Definition
open import Data.Nat.Order
open import Data.Nat.Property
open import Data.List
open import Function hiding (_$_)

private
  instance _ = Monoid⊔

freshℕ : (l : List ℕ) → ℕ
freshℕ = suc ∘ mconcat

open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Proof
open import Collection
open import Data.Functor
open import Data.List.Functor
open import Relation.Binary
open import Operation.Binary
open import Logic
open import Proof
open import Function.Proof
open import Data.Nat.Proof

freshℕ-not-stale : (l : List ℕ)
  → --------------------------------------
  freshℕ l ∉ l
freshℕ-not-stale l fresh∈l = contradiction
  where m-≤-concat : freshℕ l ≤ mconcat l
        m-≤-concat =
          mconcat-preserv
            (λ x y → postfix (flip max y) x)
            (λ x → postfix (max x))
            l (freshℕ l) fresh∈l
        contradiction : ⊥
        contradiction with go
          where go : ∃ λ x → x +1 == x
                go = mconcat l ,
                     antisym m-≤-concat (postfix suc {_≤_} (mconcat l))
        contradiction | _ , ()
