{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Property where

open import Data.Nat.Definition
open import Data.Nat.Arithmetic
open import Data.Nat.Order

open import Proposition.Identity
  renaming (Idₚ to Id) using (_==_; ap)
open import Proposition.Decidable
  using (Decidable; true; false; decide)
open import Function.Property
  using (Injective; inj)
open import Function.Proof

open import Proof
open import Operation.Binary.Property
open import Data.Nat.Proof
open import Relation.Binary.Property
open import Logic using (∨right)

instance
  Injective-suc : Injective suc
  inj ⦃ Injective-suc ⦄ (Id.refl (suc m)) = refl m

  Decidableℕ== : ∀ {n m : ℕ} → Decidable (n == m)
  Decidableℕ== {zero} {zero} = true (refl zero)
  Decidableℕ== {zero} {suc n} = false λ ()
  Decidableℕ== {suc m} {zero} = false λ ()
  Decidableℕ== {suc m} {suc n} with decide (m == n)
  Decidableℕ== {suc m} {suc n} | true n==m = true (ap suc n==m)
  Decidableℕ== {suc m} {suc n} | false ¬n==m =
    false λ { (Id.refl (suc m)) → ¬n==m (refl m) }

  Postfix-+-left-< : ∀ {n} → UniversalPostfix (suc n +_) _<_
  UniversalPostfix.postfix (Postfix-+-left-< {zero}) = postfix suc ⦃ Postfix-suc-< ⦄
  UniversalPostfix.postfix (Postfix-+-left-< {suc n}) x =
    proof x
      〉 _<_ 〉 suc n + x   :by: postfix (suc n +_) x
      〉 _<_ 〉 suc (suc n + x)
        :by: postfix suc ⦃ Postfix-suc-< ⦄ (suc n + x)
    qed

  Postfix-+-right-< : ∀ {n} → UniversalPostfix (_+ suc n) _<_
  UniversalPostfix.postfix (Postfix-+-right-< {n}) x =
    proof x
      〉 _<_ 〉 suc n + x :by: postfix (suc n +_) x
      〉 _==_ 〉 x + suc n :by: comm (suc n) x
    qed

  Postfix-+-left-≤ : ∀ {n} → UniversalPostfix (n +_) _≤_
  UniversalPostfix.postfix (Postfix-+-left-≤ {zero}) x = refl x
  UniversalPostfix.postfix (Postfix-+-left-≤ {suc n}) x =
    ∨right (postfix (suc n +_) x)

  Postfix-+-right-≤ : ∀ {n} → UniversalPostfix (_+ n) _≤_
  UniversalPostfix.postfix (Postfix-+-right-≤ {n}) x =
    proof x
      〉 _≤_ 〉 n + x :by: postfix (n +_) x
      〉 _==_ 〉 x + n :by: comm n x
    qed

  Postfix-*-left-≤ : ∀ {n} → UniversalPostfix (suc n *_) _≤_
  UniversalPostfix.postfix (Postfix-*-left-≤ {n}) x =
    postfix (_+ n * x) ⦃ Postfix-+-right-≤ ⦄ x

  Postfix-*-right-≤ : ∀ {n} → UniversalPostfix (_* suc n) _≤_
  UniversalPostfix.postfix (Postfix-*-right-≤ {n}) x =
    proof x
      〉 _≤_ 〉 suc n * x :by: postfix (suc n *_) ⦃ Postfix-*-left-≤ {n} ⦄ x
      〉 _==_ 〉 x * suc n :by: comm (suc n) x
    qed
