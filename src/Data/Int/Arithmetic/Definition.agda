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

-- infixl 140 _*_
-- _*_ : (x y : ℤ) → ℤ

-- _*ℕ×ℕ_ : (x y : ℕ × ℕ) → ℕ × ℕ
-- (m₀ ℤ, m₁) *ℕ×ℕ (n₀ ℤ, n₁) = (m₀ ℕ.* n₀ ℕ.+ m₁ ℕ.* n₁) ℤ,
--                              (m₀ ℕ.* n₁ ℕ.+ m₁ ℕ.* n₀)

-- checked-* : QuotBinOp ℤ-impl _*ℕ×ℕ_
-- QuotBinOp.preserv checked-*
--   {m₀ ℤ, m₁}{m₀' ℤ, m₁'}{n₀ ℤ, n₁}{n₀' ℤ, n₁'} p₀ p₁ =
--   ⟶ (ℤ≈↔ℤ≈' {(m₀ ℤ, m₁) *ℕ×ℕ (n₀ ℤ, n₁)}{(m₀' ℤ, m₁') *ℕ×ℕ (n₀' ℤ, n₁')}) (
--   proof (m₀ ℕ.* n₀ ℕ.+ m₁ ℕ.* n₁) ℕ.+ (m₀' ℕ.* n₁' ℕ.+ m₁' ℕ.* n₀')
--     === (m₀' ℕ.* n₀' ℕ.+ m₁' ℕ.* n₁') ℕ.+ (m₀ ℕ.* n₁ ℕ.+ m₁ ℕ.* n₀)
--       :by: {!!}
--   qed)
  

-- _*_ = QuotBinOp._⊙_ checked-*
