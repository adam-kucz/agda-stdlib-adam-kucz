{-# OPTIONS --exact-split --safe #-}
module Data.Nat.Proof where

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Order

open import Universes
open import Relation.Binary.Property
open import Operation.Binary.Property
open import Logic
open import Proof
open import Function.Proof

open Composable ⦃ ... ⦄ public

module Composable-< where
  open MakeTransComposable _<_ ⦃ Transitive< ⦄ public

instance
  Composable-<-≤ : Composable 𝒰₀ _<_ _≤_
  Composable-≤-< : Composable 𝒰₀ _≤_ _<_
  Relating-min-right : ∀ {n} → Relating (min n) _≤_ _≤_
  Relating-min-left : ∀ {n} → Relating (λ m → min m n) _≤_ _≤_

Composable.rel Composable-<-≤ = _<_
Composable.compose Composable-<-≤ (x≤y , x≠y) y≤z =
  trans x≤y y≤z , trans≠ (x≤y , x≠y) y≤z
  where trans≠ : (p : n < m)(q : m ≤ k) → n ≠ k
        trans≠ (z≤ 0 , 0≠0) (z≤ m) _ = 0≠0 $ refl 0
        trans≠ (s≤s n≤m , n+1≠m+1) (s≤s q) r =
          trans≠ (n≤m , λ n==m → n+1≠m+1 $ ap suc n==m) q $ ap pred r

Composable.rel Composable-≤-< = _<_
Composable.compose Composable-≤-< x≤y (y≤z , y≠z) =
  trans x≤y y≤z , trans≠ x≤y (y≤z , y≠z)
  where trans≠ : (p : n ≤ m)(q : m < k) → n ≠ k
        trans≠ (z≤ m) (z≤ 0 , 0≠0) _ = 0≠0 $ refl 0
        trans≠ (s≤s q) (s≤s n≤m , n+1≠m+1) r =
          trans≠ q (n≤m , λ n==m → n+1≠m+1 $ ap suc n==m) $ ap pred r

rel-preserv ⦃ Relating-min-right {zero} ⦄ _ = refl 0
rel-preserv ⦃ Relating-min-right {n +1} ⦄ {zero} {b} rab =
  z≤ min (n +1) b
rel-preserv ⦃ Relating-min-right {n +1} ⦄ {a +1} {b +1} rab =
  s≤s $ rel-preserv ⦃ Relating-min-right ⦄ $ ap pred rab

rel-preserv ⦃ Relating-min-left {n} ⦄ {a} {b} a≤b =
  proof min a n
    〉 _==_ 〉 min n a :by: comm a n
    〉 _≤_ 〉 min n b :by: rel-preserv a≤b
    〉 _==_ 〉 min b n :by: comm n b
  qed

open import Data.Nat.Arithmetic

instance
  Postfix+- : UniversalPostfix (m +_) _≤_
  Postfix-+ : UniversalPostfix (_+ m) _≤_
  Postfix*- : UniversalPostfix ((m +1) *_) _≤_
  Postfix-* : UniversalPostfix (_* (m +1)) _≤_
  Prefix- : UniversalPrefix (_- m) _≤_

UniversalPostfix.postfix (Postfix+- {zero}) n = refl n
UniversalPostfix.postfix (Postfix+- {m +1}) n =
  proof n
    〉 _≤_ 〉 m + n    :by: UniversalPostfix.postfix Postfix+- n
    〉 _≤_ 〉 m + n +1 :by: -≤self+1 (m + n)
  qed

UniversalPostfix.postfix (Postfix-+ {m}) n =
  proof n
    〉 _≤_ 〉 m + n  :by: postfix (m +_) n
    〉 _==_ 〉 n + m :by: comm m n
  qed

UniversalPostfix.postfix (Postfix*- {m}) n =
  postfix (_+ m * n) ⦃ Postfix-+ ⦄ n

UniversalPostfix.postfix (Postfix-* {m}) n =
  proof n
    〉 _≤_ 〉 (m +1) * n  :by: postfix ((m +1) *_) ⦃ Postfix*- {m} ⦄ n
    〉 _==_ 〉 n * (m +1) :by: comm (m +1) n
  qed

UniversalPrefix.prefix (Prefix- {0}) = refl
UniversalPrefix.prefix (Prefix- {m +1}) 0 = refl 0
UniversalPrefix.prefix (Prefix- {m +1}) (n +1) =
  proof n - m 〉 _≤_ 〉 n    :by: prefix (_- m) ⦃ Prefix- {m} ⦄ n
              〉 _≤_ 〉 n +1 :by: postfix suc n
  qed
