{-# OPTIONS --exact-split --prop #-}
module Data.Nat.Operation where

open import Structure.Monoid
open import Data.Nat.Definition
open import Data.Nat.Order
open import Data.List
open import Function hiding (_$_)

private
  instance
    MaxMonoid : Monoid ℕ

MaxMonoid = record { e = 0; _∙_ = max }

freshℕ : (l : List ℕ) → ℕ
freshℕ = suc ∘ mconcat

open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Proof
open import Data.Collection
open import Data.Functor
open import Data.List.Functor
open import Relation.Binary
open import Operation.Binary
open import Logic
open import Proof

freshℕ-not-stale : (l : List ℕ)
  → --------------------------------------
  freshℕ l ∉ l
freshℕ-not-stale l fresh∈l = contradiction
  where ≤max' : ∀ x y → y ≤ max x y
        ≤max' x y =
          proof y
            〉 _≤_ 〉 max y x  :by: ≤max y x
            〉 _==_ 〉 max x y :by: comm y x
          qed
        m-≤-concat : freshℕ l ≤ mconcat l
        m-≤-concat = mconcat-preserv ≤max ≤max' l (freshℕ l) fresh∈l
        contradiction : ⊥
        contradiction with go
          where go : ∃ λ x → x +1 ≤ x
                go = mconcat l , m-≤-concat
        contradiction | x , ∨right q = irrefl (x +1) (-<s q)
