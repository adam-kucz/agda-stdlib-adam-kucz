{-# OPTIONS --exact-split --safe #-}
module Data.Nat.Property where

open import Data.Nat.Definition
open import Data.Nat.Arithmetic
open import Data.Nat.Order
open import Data.Nat.Syntax
open Pattern

open import Type.Decidable
open import Type.Comparable
open import Function.Property

open import Operation.Binary.Property
open import Relation.Binary.Property
open import Logic
open import Proof
open import Function.Proof
open import Data.Nat.Proof

instance
  Surjective-pred : Surjective pred
  Decidableℕ== : Decidable (n == m)
  Relating-+-left-≤ : Relating (m +_) _≤_ _≤_
  Relating-+-right-≤ : Relating (_+ m) _≤_ _≤_
  Relating-+-left-< : Relating (m +_) _<_ _<_
  Relating-+-right-< : Relating (_+ m) _<_ _<_
  Relating-2-+-≤-≤ : Relating-2 _+_ _≤_ _≤_ _≤_
  Relating-2-+-<-≤ : Relating-2 _+_ _<_ _≤_ _<_
  Relating-2-+-≤-< : Relating-2 _+_ _≤_ _<_ _<_
  Postfix-+-left-< : UniversalPostfix (suc n +_) _<_
  Postfix-+-right-< : UniversalPostfix (_+ suc n) _<_
  Postfix-+-left-≤ : UniversalPostfix (n +_) _≤_
  Postfix-+-right-≤ : UniversalPostfix (_+ n) _≤_
  Postfix-*-left-≤ : UniversalPostfix (suc n *_) _≤_
  Postfix-*-right-≤ : UniversalPostfix (_* suc n) _≤_
  Prefix-min-≤ : UniversalPrefix (min n) _≤_
  Prefix-min-2-≤ : UniversalPrefix (λ — → min — n) _≤_
  Postfix-max-≤ : UniversalPostfix (max n) _≤_
  Postfix-max-2-≤ : UniversalPostfix (λ — → max — n) _≤_
  Comparable< : Comparable _<_ m n

surj ⦃ Surjective-pred ⦄ y = suc y , refl y

Decidableℕ== {zero} {zero} = true (refl zero)
Decidableℕ== {zero} {suc n} = false λ ()
Decidableℕ== {suc m} {zero} = false λ ()
Decidableℕ== {suc m} {suc n} with decide (m == n)
Decidableℕ== {suc m} {suc n} | true n==m = true (ap suc n==m)
Decidableℕ== {suc m} {suc n} | false ¬n==m =
  false λ { (Id.refl (suc m)) → ¬n==m (refl m) }

rel-preserv ⦃ Relating-+-left-≤ {m} ⦄ (z≤ k) =
  proof m + 0
    === m        :by: right-unit m     [: _==_ ]
    〉 _≤_ 〉 m + k :by: postfix (_+ k) m
  qed
rel-preserv ⦃ Relating-+-left-≤ {m} ⦄ (s≤s {n}{k} n≤k) =
  proof m + (n +1)
    === (m +1) + n    :by: +-suc m n
    〉 _≤_ 〉 (m +1) + k :by: s≤s $ rel-preserv ⦃ Relating-+-left-≤ ⦄ n≤k
    === m + (k +1)    :by: sym $ +-suc m k
  qed
rel-preserv ⦃ Relating-+-right-≤ {m} ⦄ {a}{b} a≤b =
  proof a + m
    === m + a     :by: comm a m
    〉 _≤_ 〉  m + b :by: ap (m +_) a≤b
    === b + m     :by: comm m b
  qed

rel-preserv ⦃ Relating-+-left-< ⦄ (z≤ zero , a≠b) =
  ⊥-recursion _ $ a≠b $ refl 0
rel-preserv ⦃ Relating-+-left-< {m} ⦄ (z≤ a +1 , a≠b) =
  proof m + 0
    === m             :by: right-unit m
    〉 _<_ 〉 m +1       :by: postfix suc m
    〉 _≤_ 〉 (m +1) + a :by: postfix (_+ a) (m +1)
    === m + (a +1)    :by: sym $ +-suc m a
  qed
rel-preserv ⦃ Relating-+-left-< {m} ⦄ (s≤s {a}{b} a≤b , a≠b) =
  proof m + (a +1)
    === m + a +1   :by: +-suc m a
    〉 _<_ 〉 m + b +1
      :by: s<s $
           rel-preserv ⦃ Relating-+-left-< {m} ⦄
           (a≤b , λ { (Id.refl a) → a≠b $ refl (a +1)})
    === m + (b +1) :by: sym $ +-suc m b
  qed

rel-preserv ⦃ Relating-+-right-< {m} ⦄ {a}{b} a<b =
  proof a + m
    ===     m + a :by: comm a m
    〉 _<_ 〉 m + b  :by: ap (m +_) a<b
    ===     b + m :by: comm m b
  qed

rel-preserv-2 ⦃ Relating-2-+-≤-≤ ⦄ {x}{x'}{y}{y'} x≤x' y≤y' = 
  proof x + y
    〉 _≤_ 〉 x' + y  :by: ap (_+ y) x≤x'
    〉 _≤_ 〉 x' + y' :by: ap (x' +_) y≤y'
  qed

rel-preserv-2 ⦃ Relating-2-+-<-≤ ⦄ {x}{x'}{y}{y'} x<x' y≤y' = 
  proof x + y
    〉 _<_ 〉 x' + y  :by: ap (_+ y) x<x'
    〉 _≤_ 〉 x' + y' :by: ap (x' +_) y≤y'
  qed
rel-preserv-2 ⦃ Relating-2-+-≤-< ⦄ {x}{x'}{y}{y'} x≤x' y<y' = 
  proof x + y
    〉 _≤_ 〉 x' + y  :by: ap (_+ y) x≤x'  [: _≤_ ]
    〉 _<_ 〉 x' + y' :by: ap (x' +_) y<y'
  qed

UniversalPostfix.postfix (Postfix-+-left-< {n}) x =
  proof x
    〉 _≤_ 〉 n + x    :by: postfix (n +_) x [: _≤_ ]
    〉 _<_ 〉 n + x +1 :by: -<self+1 (n + x)
  qed

UniversalPostfix.postfix (Postfix-+-right-< {n}) x =
  proof x
    〉 _<_ 〉 (n +1) + x  :by: postfix (n +1 +_) x 
    === x + (n +1) :by: comm (n +1) x
  qed

Postfix-+-left-≤ = Postfix+-
Postfix-+-right-≤ = Postfix-+
Postfix-*-left-≤ {m} = Postfix*- {m}
Postfix-*-right-≤ = Postfix-*

UniversalPrefix.prefix (Prefix-min-≤ {n}) = go n
  where go : ∀ n m → min n m ≤ m
        go zero m = z≤ m
        go (n +1) zero = z≤ 0
        go (n +1) (m +1) = ap suc $ go n m

UniversalPostfix.postfix (Postfix-max-≤ {n}) = go n
  where go : ∀ n m → m ≤ max n m
        go zero m = refl m
        go (n +1) zero = z≤ n +1
        go (n +1) (m +1) = ap suc $ go n m

UniversalPrefix.prefix (Prefix-min-2-≤ {n}) m =
  proof min m n
    === min n m :by: comm m n          [: _==_ ]
    〉 _≤_ 〉 m    :by: prefix (min n) ⦃ Prefix-min-≤ ⦄ m
  qed

UniversalPostfix.postfix (Postfix-max-2-≤ {n}) m =
  proof m
    〉 _≤_ 〉 max n m :by: postfix (max n) m
    === max m n    :by: comm n m
  qed

Comparable< {zero} {zero} = eq (Id.refl 0)
Comparable< {zero} {n +1} = lt (z<s n)
Comparable< {m +1} {zero} = gt (z<s m)
Comparable< {m +1} {n +1} = suc-step Comparable<
  where suc-step : ∀ {m n}
          (c : Comparable _<_ m n)
          → -----------------------------
          Comparable _<_ (m +1) (n +1)
        suc-step (lt p) = lt (ap suc p)
        suc-step (eq p) = eq (ap suc p)
        suc-step (gt p) = gt (ap suc p)

open import Structure.Monoid.Definition

Monoid⊔ : Monoid ℕ
Monoid⊔ = record { e = 0; _∙_ = _⊔_ }
