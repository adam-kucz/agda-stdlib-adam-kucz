{-# OPTIONS --exact-split --safe --prop #-}
module Data.Int.Arithmetic.Definition where

open import Data.Int.Definition
open import Data.Int.Syntax
open import Data.Int.Property

import Data.Nat as ℕ
open ℕ using (ℕ; m; n)
open import Type.Sum hiding (_,_)

infixr 135 -_
-_ : (x : ℤ) → ℤ
- (m ℤ, n , valid) = n ℤ, m , rev-valid valid

infixl 130 _+_ _-_
_+_ _-_ : (x y : ℤ) → ℤ

_+ℕ×ℕ_ : (x y : ℕ × ℕ) → ℕ × ℕ
(m₀ ℤ, m₁) +ℕ×ℕ (n₀ ℤ, n₁) = (m₀ ℕ.+ n₀) ℤ, (m₁ ℕ.+ n₁)

open import Type.Quotient
open import Operation.Binary
open import Logic
open import Proof

checked-+ : QuotBinOp ℤ-impl _+ℕ×ℕ_
QuotBinOp.preserv checked-+
  {m₀ ℤ, m₁}{m₀' ℤ, m₁'}{n₀ ℤ, n₁}{n₀' ℤ, n₁'} pₘ pₙ =
  ⟶ (ℤ≈↔ℤ≈' {(m₀ ℤ, m₁) +ℕ×ℕ (n₀ ℤ, n₁)}{(m₀' ℤ, m₁') +ℕ×ℕ (n₀' ℤ, n₁')}) (
  proof m₀ ℕ.+ n₀ ℕ.+ (m₁' ℕ.+ n₁')
    === m₀ ℕ.+ n₀ ℕ.+ m₁' ℕ.+ n₁'   :by: assoc _ m₁' n₁'
    === m₀ ℕ.+ m₁' ℕ.+ n₀ ℕ.+ n₁'   :by: ap (ℕ._+ n₁') $ swap' m₀ n₀ m₁'
    === m₀ ℕ.+ m₁' ℕ.+ (n₀ ℕ.+ n₁') :by: sym $ assoc _ n₀ n₁'
    === m₀' ℕ.+ m₁ ℕ.+ (n₀' ℕ.+ n₁)
      :by: ap2 ℕ._+_ (⟵ (ℤ≈↔ℤ≈' {m₀ ℤ, m₁}{m₀' ℤ, m₁'}) pₘ)
                     (⟵ (ℤ≈↔ℤ≈' {n₀ ℤ, n₁}{n₀' ℤ, n₁'}) pₙ)
    === m₀' ℕ.+ m₁ ℕ.+ n₀' ℕ.+ n₁   :by: assoc _ n₀' n₁
    === m₀' ℕ.+ n₀' ℕ.+ m₁ ℕ.+ n₁   :by: ap (ℕ._+ n₁) $ swap' m₀' m₁ n₀'
    === m₀' ℕ.+ n₀' ℕ.+ (m₁ ℕ.+ n₁) :by: sym $ assoc _ m₁ n₁
  qed)

_+_ = QuotBinOp._⊙_ checked-+

x - y = x + - y

infixl 140 _*_
_*_ : (x y : ℤ) → ℤ

_*ℕ×ℕ_ : (x y : ℕ × ℕ) → ℕ × ℕ
(m₀ ℤ, m₁) *ℕ×ℕ (n₀ ℤ, n₁) = (m₀ ℕ.* n₀ ℕ.+ m₁ ℕ.* n₁) ℤ,
                             (m₀ ℕ.* n₁ ℕ.+ m₁ ℕ.* n₀)

open import Proposition.Decidable
open import Data.Nat.Arithmetic.Subtraction.Unsafe renaming (_-_ to _ℕ-_)

checked-* : QuotBinOp ℤ-impl _*ℕ×ℕ_
-- safe to do super-split because we are in Prop
QuotBinOp.preserv checked-*
  {m₀ ℤ, m₁}{m₀' ℤ, m₁'}{n₀ ℤ, n₁}{n₀' ℤ, n₁'} q₀ q₁ = go
  where m₀n₀ = m₀ ℕ.* n₀
        m₁n₁ = m₁ ℕ.* n₁
        m₀n₁ = m₀ ℕ.* n₁
        m₁n₀ = m₁ ℕ.* n₀
        m₀n₀' = m₀' ℕ.* n₀'
        m₁n₁' = m₁' ℕ.* n₁'
        m₀n₁' = m₀' ℕ.* n₁'
        m₁n₀' = m₁' ℕ.* n₀'
        same-m : m₁ ℕ.≤ m₀ ↔ m₁' ℕ.≤ m₀'
        ⟶ same-m p = ∧right $ ℤ-class-0-nneg (
          proof ℤ-class (m₀' ℤ, m₁')
            === ℤ-class (m₀ ℤ, m₁) :by: sym q₀
            === m₀ ℕ- m₁ ℤ, 0      :by: ⟶ ℤ-class-nneg p
          qed)
        ⟵ same-m q = ∧right $ ℤ-class-0-nneg (
          proof ℤ-class (m₀ ℤ, m₁)
            === ℤ-class (m₀' ℤ, m₁') :by: q₀
            === m₀' ℕ- m₁' ℤ, 0      :by: ⟶ ℤ-class-nneg q
          qed)
        same-n : n₁ ℕ.≤ n₀ ↔ n₁' ℕ.≤ n₀'
        ⟶ same-n p = ∧right $ ℤ-class-0-nneg (
          proof ℤ-class (n₀' ℤ, n₁')
            === ℤ-class (n₀ ℤ, n₁) :by: sym q₁
            === n₀ ℕ- n₁ ℤ, 0      :by: ⟶ ℤ-class-nneg p
          qed)
        ⟵ same-n q = ∧right $ ℤ-class-0-nneg (
          proof ℤ-class (n₀ ℤ, n₁)
            === ℤ-class (n₀' ℤ, n₁') :by: q₁
            === n₀' ℕ- n₁' ℤ, 0      :by: ⟶ ℤ-class-nneg q
          qed)
        go : ℤ-class (m₀n₀ ℕ.+ m₁n₁ ℤ, m₀n₁ ℕ.+ m₁n₀) ==
             ℤ-class (m₀n₀' ℕ.+ m₁n₁' ℤ, m₀n₁' ℕ.+ m₁n₀')
        go with decide (m₁ ℕ.≤ m₀) | decide (m₁' ℕ.≤ m₀')
              | decide (n₁ ℕ.≤ n₀) | decide (n₁' ℕ.≤ n₀')
        ... | true p₀ | true p₁ | true p | true p₂ = {!!}
        ... | true p₀ | true p₁ | false ¬p | false ¬p₁ = {!!}
        ... | false ¬p₀ | false ¬p₁ | true p | true p₁ = {!!}
        ... | false ¬p₀ | false ¬p₁ | false ¬p | false ¬p₂ = {!!}
        ... | true p₀ | false ¬p₁ | z | w =
          ⊥-recursion _ $ ¬p₁ $ ⟶ same-m p₀
        ... | false ¬p₀ | true p₁ | z | w =
          ⊥-recursion _ $ ¬p₀ $ ⟵ same-m p₁
        ... | true p₀ | true p₁ | true p₂ | false ¬p₃ =
          ⊥-recursion _ $ ¬p₃ $ ⟶ same-n p₂
        ... | false ¬p₀ | false ¬p₁ | true p₂ | false ¬p₃ =
          ⊥-recursion _ $ ¬p₃ $ ⟶ same-n p₂
        ... | true p₀ | true p₁ | false ¬p₂ | true p₃ =
          ⊥-recursion _ $ ¬p₂ $ ⟵ same-n p₃
        ... | false ¬p₀ | false ¬p₁ | false ¬p₂ | true p₃ =
          ⊥-recursion _ $ ¬p₂ $ ⟵ same-n p₃

  
_*_ = QuotBinOp._⊙_ checked-*
