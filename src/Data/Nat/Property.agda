{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Property where

open import Data.Nat.Definition
open import Data.Nat.Arithmetic
open import Data.Nat.Order
open import Data.Nat.Syntax
open Pattern

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
  UniversalPostfix.postfix (Postfix-+-left-< {zero}) =
    postfix suc ⦃ Postfix-suc-< ⦄
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

+-inv : ∀ m k → m + k - k [ postfix (m +_) k ] == m
+-inv 0 0 = refl 0
+-inv 0 (k +1) = +-inv 0 k
+-inv (m +1) 0 = right-unit (suc m)
+-inv (m +1) (k +1) =
  proof m + (k +1) - k [ _ ]
    === m + k +1 - k [ _ ]
      :by: -== (+-suc m k) (refl k)
    === m +1 + k - k [ _ ]
      :by: Id.refl _
    === m +1
      :by: +-inv (m +1) k
  qed

postfix-sub-< : ∀ {m n} k {p p'}
  (q : m < n)
  → --------------------
  m - k [ p ] < n - k [ p' ]
postfix-sub-< {zero} {_ +1} zero _ = z<s
postfix-sub-< {zero} {_ +1} (_ +1) {Logic.∨left ()}
postfix-sub-< {zero} {_ +1} (_ +1) {∨right ()}
postfix-sub-< {_ +1} {_ +1} zero q = q
postfix-sub-< {m +1} {n +1} (k +1) q = postfix-sub-< k (s<s→-<- q)
