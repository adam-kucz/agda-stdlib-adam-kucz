{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinNat.Property where

open import Data.FinNat.Definition
open import Data.Nat as Nat
  using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤_; s<s; z<s_; s<s→-<-)

open import Proposition.Decidable
open import Function hiding (_$_)
open import Logic
open import Proof
open import Function.Proof

toFinℕ== : ∀{n n' m m'}
  (pn : n == n')
  (pm : m == m')
  (q : suc n ≤ m)
  → ------------------------
  let q' = Id.coe (ap2 (λ n m → suc n ≤ m) pn pm) q in
  toFinℕ n q Het.== toFinℕ n' q'
toFinℕ== (Id.refl n) (Id.refl m) q = Het.refl (toFinℕ n q)

instance
  Injective-suc : ∀ {n} → Injective (Finℕ.suc {n})
  inj ⦃ Injective-suc ⦄ (Het.refl (suc x)) = Id.refl x

  Decidable==Finℕ : ∀ {n} {a b : Finℕ n} → Decidable (a == b)
  Decidable==Finℕ {a = zero} {zero} = true (refl 0)
  Decidable==Finℕ {a = zero} {suc b} = false λ ()
  Decidable==Finℕ {a = suc a} {zero} = false λ ()
  Decidable==Finℕ {a = suc a} {suc b} with decide (a == b)
  Decidable==Finℕ {suc a} {suc b} | true a==b = true (ap suc a==b)
  Decidable==Finℕ {suc a} {suc b} | false ¬a==b =
    false λ { (Id.refl _) → ¬a==b $ refl b }

  Injective-toℕ : ∀ {n} → Injective (toℕ {n})
  inj ⦃ Injective-toℕ ⦄ {x = zero} {zero} _ = refl zero
  inj ⦃ Injective-toℕ ⦄ {x = suc x} {suc y} fx==fy = 
    ap suc $ inj ⦃ Injective-toℕ ⦄ $ subrel $
    inj {f = suc} fx==fy

toℕ< : ∀ {n} (a : Finℕ n) → suc (toℕ a) ≤ n
toℕ< {suc n} zero = postfix (Nat._+ n) 1
toℕ< (suc a) = ap suc (toℕ< a)

toℕ-maxFinℕ : ∀ n → toℕ (maxFinℕ n) == n
toℕ-maxFinℕ zero = refl 0
toℕ-maxFinℕ (suc n) = ap suc (toℕ-maxFinℕ n)

toℕ-toFinℕ : ∀ {m n} (n<m : suc n ≤ m) → toℕ (toFinℕ n n<m) == n
toℕ-toFinℕ {suc m} (s≤s (z≤ m)) = refl 0
toℕ-toFinℕ {suc m} (s≤s (s≤s n<m)) = ap suc $ toℕ-toFinℕ $ s≤s n<m

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
