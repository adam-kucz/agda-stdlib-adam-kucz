{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Definition where

open import Universes
open import Proposition.Identity hiding (refl)
open import Type.Quotient
import Type.Sum
open Type.Sum
open Type.Sum renaming (_,_ to _ℤ,_) using () public
open import Data.Nat
open import Relation.Binary

_ℤ≈_ _ℤ≈'_ : BinRel 𝒰₀ (ℕ × ℕ)
-- a - b == c - d ↔ a + d == c + b
(a₀ , a₁) ℤ≈ (b₀ , b₁) = a₀ + b₁ == b₀ + a₁

ℤ≈++-invariant : ∀ m n → (m , n) ℤ≈ (m +1 , n +1)
ℤ≈++-invariant = +-suc

open import Function hiding (_$_)

ℤ-class : ℕ × ℕ → ℕ × ℕ
ℤ-class (0 , n) = (0 , n)
ℤ-class (m +1 , 0) = (m +1 , 0)
ℤ-class (m +1 , n +1) = ℤ-class (m , n)

private
  instance
    ℤ-class-indempotent : Idempotent ℤ-class

idemp ⦃ ℤ-class-indempotent ⦄ (0 , n) = refl (0 , n)
idemp ⦃ ℤ-class-indempotent ⦄ (m +1 , 0) = refl (m +1 , 0)
idemp ⦃ ℤ-class-indempotent ⦄ (m +1 , n +1) =
  idemp ⦃ ℤ-class-indempotent ⦄ (m , n)

x ℤ≈' y = ℤ-class x == ℤ-class y

open import Data.Nat.Arithmetic.Subtraction.Unsafe
open import Logic renaming (_,_ to _∧,_)
open import Proof
open import Function.Proof
open import Operation.Binary hiding (left-inverse; right-inverse)

ℤ-class-nneg : ∀{m n} → n ≤ m ↔ ℤ-class (m , n) == (m - n , 0)
⟶ ℤ-class-nneg (z≤ 0) = refl (0 , 0)
⟶ ℤ-class-nneg (z≤ (m +1)) = refl (m +1 , 0)
⟶ ℤ-class-nneg (s≤s p) = ⟶ ℤ-class-nneg p
⟵ (ℤ-class-nneg {0} {0}) (Id.refl (0 ℤ, 0)) = refl 0
⟵ (ℤ-class-nneg {m +1} {0}) q = z≤ m +1
⟵ (ℤ-class-nneg {m +1} {n +1}) q = ap suc $ ⟵ ℤ-class-nneg q

ℤ-class-npos : ∀{m n} → m ≤ n ↔ ℤ-class (m , n) == (0 , n - m)
⟶ ℤ-class-npos (z≤ n) = refl (0 , n)
⟶ ℤ-class-npos (s≤s p) = ⟶ ℤ-class-npos p
⟵ (ℤ-class-npos {zero} {n}) q = z≤ n
⟵ (ℤ-class-npos {m +1} {n +1}) q = ap suc $ ⟵ ℤ-class-npos q

open import Proposition.Decidable

is-ℤ-class-fixpoint : ∀{x} →
  x == ℤ-class x ↔ ∃ λ m → x == (0 , m) ∨ x == (m , 0)
⟶ (is-ℤ-class-fixpoint {m ℤ, n}) p with decide (n ≤ m)
... | true n≤m = m ∧, ∨right $ ap (m ℤ,_) prf
  where prf : n == 0
        prf = proof n === pr₂ (m ℤ, n)           :by: refl n
                      === pr₂ (ℤ-class (m ℤ, n)) :by: ap pr₂ p
                      === pr₂ (m - n ℤ, 0)
                        :by: ap pr₂ $ ⟶ ℤ-class-nneg n≤m
                      === 0                      :by: refl 0
              qed
... | false ¬n≤m = n ∧, ∨left $ ap (_ℤ, n) prf
  where prf : m == 0
        prf = proof m
                === pr₁ (m ℤ, n)           :by: refl m
                === pr₁ (ℤ-class (m ℤ, n)) :by: ap pr₁ p
                === 0
                  :by: ap pr₁ $ ⟶ ℤ-class-npos $ total-other ¬n≤m
              qed
⟵ is-ℤ-class-fixpoint (m ∧, ∨left (Id.refl (0 ℤ, m))) = refl (0 ℤ, m)
⟵ is-ℤ-class-fixpoint (0 ∧, ∨right (Idₚ.refl (0 ℤ, 0))) = refl (0 ℤ, 0)
⟵ is-ℤ-class-fixpoint (m +1 ∧, ∨right (Idₚ.refl (m +1 ℤ, 0))) =
  refl (m +1 ℤ, 0)

ℤ≈↔ℤ≈' : ∀{x y} → x ℤ≈ y ↔ x ℤ≈' y
⟶ (ℤ≈↔ℤ≈' {0 , m₁} {n₀ , .(n₀ + m₁)}) (Idₚ.refl .(n₀ + m₁)) =
  proof 0 , m₁
    === 0 , m₁ + n₀ - n₀
      :by: ap (0 ,_) $ sym $ subrel $ left-inverse-of (_+ n₀) m₁
    === 0 , n₀ + m₁ - n₀
      :by: ap (λ — → (0 , — - n₀)) $ comm m₁ n₀
    === ℤ-class (n₀ , n₀ + m₁)
      :by: sym $ ⟶ ℤ-class-npos $ postfix (_+ m₁) n₀
  qed
⟶ (ℤ≈↔ℤ≈' {m₀ +1 , .(m₀ + n₁ +1)} {0 , n₁}) (Id.refl .(m₀ + n₁ +1)) =
  proof ℤ-class (m₀ +1 , m₀ + n₁ +1)
    === 0 , m₀ + n₁ - m₀ :by: ⟶ ℤ-class-npos $ s≤s (postfix (_+ n₁) m₀)
    === 0 , n₁ + m₀ - m₀ :by: ap (λ — → 0 , — - m₀) $ comm m₀ n₁
    === 0 , n₁           :by: ap (0 ,_) $ subrel $ left-inverse-of (_+ m₀) n₁
  qed
⟶ (ℤ≈↔ℤ≈' {m₀ +1 , zero} {n₀ +1 , zero}) p with prf
  where prf : m₀ +1 == n₀ +1
        prf = 
          proof m₀ +1
            === m₀ +1 + 0 :by: sym $ right-unit (m₀ +1)
            === n₀ +1 + 0 :by: p
            === n₀ +1     :by: right-unit (n₀ +1)
          qed
... | Idₚ.refl (m₀ +1) = Idₚ.refl (m₀ +1 , zero)
⟶ (ℤ≈↔ℤ≈' {m₀ +1 , zero} {n₀ +1 , n₁ +1}) p =
  ⟶ (ℤ≈↔ℤ≈' {m₀ +1 , zero} {n₀ , n₁}) prf
  where prf : m₀ + n₁ +1 == n₀ + 0
        prf = proof m₀ + n₁ +1
                === m₀ + (n₁ +1) :by: sym $ +-suc m₀ n₁
                === n₀ + 0       :by: ap pred p
              qed
⟶ (ℤ≈↔ℤ≈' {m₀ +1 , m₁ +1} {n₀ +1 , 0}) p =
  ⟶ (ℤ≈↔ℤ≈' {m₀ , m₁} {n₀ +1 , 0}) prf
  where prf : m₀ + 0 == n₀ +1 + m₁
        prf = proof m₀ + 0
                === n₀ + (m₁ +1) :by: ap pred p
                === n₀ + m₁ +1   :by: +-suc n₀ m₁
              qed
⟶ (ℤ≈↔ℤ≈' {m₀ +1 , m₁ +1} {n₀ +1 , n₁ +1}) p =
  ⟶ (ℤ≈↔ℤ≈' {m₀ , m₁} {n₀ , n₁}) $ ap pred prf
  where prf : m₀ + n₁ +1 == n₀ + m₁ +1
        prf = proof m₀ + n₁ +1
                === m₀ + (n₁ +1) :by: sym $ +-suc m₀ n₁
                === n₀ + (m₁ +1) :by: ap pred p
                === n₀ + m₁ +1   :by: +-suc n₀ m₁
              qed
⟵ (ℤ≈↔ℤ≈' {zero , m₁} {zero , m₁}) (Idₚ.refl (0 , m₁)) = Id.refl m₁
⟵ (ℤ≈↔ℤ≈' {zero , m₁} {n₀ +1 , n₁ +1}) q =
  ap suc $ ⟵ (ℤ≈↔ℤ≈' {zero , m₁} {n₀ , n₁}) q
⟵ (ℤ≈↔ℤ≈' {m₀ +1 , m₁ +1} {zero , n₁}) q =
  ap suc $ ⟵ (ℤ≈↔ℤ≈' {m₀ , m₁} {zero , n₁}) q
⟵ (ℤ≈↔ℤ≈' {m₀ +1 , zero} {m₀ +1 , zero}) (Id.refl .(m₀ +1 , 0)) =
  refl (m₀ +1 + 0) 
⟵ (ℤ≈↔ℤ≈' {m₀ +1 , zero} {n₀ +1 , n₁ +1}) q =
  proof m₀ + (n₁ +1) +1
    === m₀ + n₁ +2 :by: ap suc $ +-suc m₀ n₁
    === n₀ + 0 +1  :by: ap suc $ ⟵ (ℤ≈↔ℤ≈' {m₀ +1 , zero} {n₀ , n₁}) q
  qed
⟵ (ℤ≈↔ℤ≈' {m₀ +1 , m₁ +1} {n₀ +1 , zero}) q =
  proof m₀ + 0 +1
    === n₀ + m₁ +2      :by: ap suc $ ⟵ (ℤ≈↔ℤ≈' {m₀ , m₁} {n₀ +1 , zero}) q
    === n₀ + (m₁ +1) +1 :by: ap suc $ sym $ +-suc n₀ m₁
  qed
⟵ (ℤ≈↔ℤ≈' {m₀ +1 , m₁ +1} {n₀ +1 , n₁ +1}) q =
  proof m₀ + (n₁ +1) +1
    === m₀ + n₁ +2      :by: ap suc $ +-suc m₀ n₁
    === n₀ + m₁ +2      :by: ap _+2 $ ⟵ (ℤ≈↔ℤ≈' {m₀ , m₁} {n₀ , n₁}) q
    === n₀ + (m₁ +1) +1 :by: ap suc $ sym $ +-suc n₀ m₁
  qed

ℤ-impl : ℕ × ℕ / _ℤ≈'_
class-of ⦃ ℤ-impl ⦄ = ℤ-class
class-def ⦃ ℤ-impl ⦄ {x}{y} = refl (ℤ-class x == ℤ-class y)

ℤ : 𝒰₀ ˙
ℤ = QuotientType ℤ-impl

to-int : ℕ × ℕ → ℤ
to-int = as-quot ⦃ ℤ-impl ⦄

open import Proposition.Sum using (_,_) public
