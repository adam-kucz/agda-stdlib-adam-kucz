{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.OrderArithmetic where

open import Data.Nat.Order
open import Data.Nat.Arithmetic
open import Data.Nat.Property

open import Proposition.Identity
  renaming (Idₚ to Id) hiding (refl)
open import Operation.Binary
open import Function.Property
open import Logic

open import Proof
open import Function.Proof
open import Data.Nat.Proof

<-add-def : ∀ {m n} →
  m < n ↔ ∃! λ k → suc k + m == n
⟶ (<-add-def {m}{suc n}) z<s =
  n , (ap suc $ right-unit n , λ y p → inj (
    proof suc y
      〉 _==_ 〉 suc (y + 0) :by: ap suc $ sym $ right-unit y
      〉 _==_ 〉 suc n :by: p
    qed))
⟶ <-add-def (s<s p) with ⟶ <-add-def p
⟶ (<-add-def {suc m}{suc n}) (s<s p) | k , (sk+n==m , uniq) =
  k , (ap suc (
         proof k + suc m
           〉 _==_ 〉 suc k + m :by: +-suc k m
           〉 _==_ 〉 n         :by: sk+n==m
         qed) ,
       λ y q → uniq y (
         proof suc y + m
           〉 _==_ 〉 y + suc m :by: sym $ +-suc y m
           〉 _==_ 〉 n         :by: inj q
         qed))
⟵ (<-add-def {m}) (k , (Id.refl _ , _)) = postfix (suc k +_) m


