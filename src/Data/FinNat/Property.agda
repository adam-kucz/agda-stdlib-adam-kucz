{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinNat.Property where

open import Data.FinNat.Definition
open import Data.Nat as Nat
  using (ℕ; suc; zero; _<_; s<s; z<s)

open import Proposition.Decidable
open import Proposition.Identity as Id
  using (_==_; refl; ap; ap')
open import Function using (_$_; _∘_)
open import Proposition.Function renaming (_$_ to _$'_) using ()
open import Logic
open import Function.Property using (Injective; inj)

instance
  Injective-suc : ∀ {n} → Injective (Finℕ.suc {n})
  inj ⦃ Injective-suc ⦄ (refl (suc x)) = refl x

  Decidable==Finℕ : ∀ {n} {a b : Finℕ n} → Decidable (a == b)
  Decidable==Finℕ {a = zero} {zero} = true (refl 0)
  Decidable==Finℕ {a = zero} {suc b} = false λ ()
  Decidable==Finℕ {a = suc a} {zero} = false λ ()
  Decidable==Finℕ {a = suc a} {suc b} with decide (a == b)
  Decidable==Finℕ {suc a} {suc b} | true a==b = true (ap' Finℕ suc a==b)
  Decidable==Finℕ {suc a} {suc b} | false ¬a==b =
    false λ { (refl _) → ¬a==b $' refl b }

  Injective-toℕ : ∀ {n} → Injective (toℕ {n})
  inj ⦃ Injective-toℕ ⦄ {x = zero} {zero} _ = refl zero
  inj ⦃ Injective-toℕ ⦄ {x = suc x} {suc y} fx==fy = 
    ap' Finℕ suc $' inj ⦃ Injective-toℕ ⦄ $' inj fx==fy

toℕ< : ∀ {n} (a : Finℕ n) → toℕ a < n
toℕ< zero = z<s
toℕ< (suc a) = s<s (toℕ< a)

toℕ-maxFinℕ : ∀ n → toℕ (maxFinℕ n) == n
toℕ-maxFinℕ zero = refl 0
toℕ-maxFinℕ (suc n) = ap suc (toℕ-maxFinℕ n)

toℕ-toFinℕ : ∀ {m n} (n<m : n < m) → toℕ (toFinℕ n n<m) == n
toℕ-toFinℕ {m = suc m} z<s = refl 0
toℕ-toFinℕ {m = suc m} (s<s n<m) = ap suc $' toℕ-toFinℕ n<m

open Nat using (-<s∨->-; -≤-↔-<s)

-- private
--   open Id using (_≠_)
--   open Id.Id using (transport)
--   open import Proposition.Wrapped
--   open import Relation.Binary using (sym)
--   open import Function.Proof using (postfix)
--   Finℕ-less≠Finℕ : ∀ {m n} (p : m < n) → Finℕ m ≠ Finℕ n
--   Finℕ-less≠Finℕ z<s p with transport Wrapped (sym p) $' wrap zero
--   Finℕ-less≠Finℕ z<s _ | (unwrap ())
--   Finℕ-less≠Finℕ {suc m} {suc n} (s<s m<n) p
--     with transport Wrapped (sym p) $' wrap (toFinℕ n (postfix suc n))
--   Finℕ-less≠Finℕ {suc m} {suc n} (s<s m<n) p | unwrap x = {!!}

-- Finℕ-type== : ∀ {m n} → m == n ↔ Finℕ m == Finℕ n
-- ⟶ Finℕ-type== (refl n) = refl (Finℕ n)
-- ⟵ (Finℕ-type== {m} {n}) q = {!!}

-- ⟵ (Finℕ-type== {m} {n}) q with -<s∨->- m n
-- ⟵ (Finℕ-type== {m} {n}) q | ∨left p =
--   ⊥-recursion (m == n) (Finℕ-less≠Finℕ p q)
-- ⟵ (Finℕ-type== {m} {n}) q | ∨right n<sm with ⟵ -≤-↔-<s n<sm
-- ⟵ (Finℕ-type== {m} {n}) q | ∨right n<sm | ∨left n==m = sym n==m
-- ⟵ (Finℕ-type== {m} {n}) q | ∨right n<sm | ∨right n<m =
--   ⊥-recursion (m == n) (Finℕ-less≠Finℕ n<m $' sym q)
