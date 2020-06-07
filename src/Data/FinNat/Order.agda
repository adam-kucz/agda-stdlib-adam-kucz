{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinNat.Order where

open import Data.FinNat.Definition
open import Data.FinNat.Arithmetic
open import Data.FinNat.Property
open import Data.Nat as ℕ
  using (ℕ; _<_; _≤_; z<s_; s<s; min)

open import PropUniverses
open import Logic
open import Proposition.Function using (_∘_)

open import Relation.Binary
open import Proposition.Decidable
open import Function.Proof
open import Proof
open import Data.Nat.Proof

private
  variable
    n m : ℕ
    a b : Finℕ n

infix 35 _<ₛ_
data _<ₛ_ : Finℕ n → Finℕ m → 𝒰₀ ᵖ where
  z<ₛs : zero {n} <ₛ suc a
  s<ₛs : (a<ₛb : a <ₛ b) → suc a <ₛ suc b

s<s→-<- : (p : suc a <ₛ suc b) → a <ₛ b
s<s→-<- (s<ₛs p) = p

instance
  Irreflexive<ₛ : Irreflexive (_<ₛ_ {n} {n})
  Asymmetirc<ₛ : Asymmetric (_<ₛ_ {n} {n})
  Transitive<ₛ : Transitive (_<ₛ_ {n} {n})
  Decidable<ₛ : ∀ {n} {a b : Finℕ n} → Decidable (a <ₛ b)
  Relating-suc-<ₛ : ∀ {n} → Relating (suc {n}) _<ₛ_ _<ₛ_
  Postfix-suc-<ₛ : ∀ {n} → UniversalPostfix (suc {n}) _<ₛ_
  Relating-maxFinℕ : Relating maxFinℕ _<_ _<ₛ_
  Relating-toℕ : Relating (toℕ {n}) _<ₛ_ _<_

irrefl ⦃ Irreflexive<ₛ ⦄ zero ()
irrefl ⦃ Irreflexive<ₛ ⦄ (suc n) sn<sn = irrefl n (s<s→-<- sn<sn)

asym ⦃ Asymmetirc<ₛ ⦄ z<ₛs ()
asym ⦃ Asymmetirc<ₛ ⦄ (s<ₛs a<b) (s<ₛs b<a) = asym b<a a<b
  
trans ⦃ Transitive<ₛ ⦄ z<ₛs (s<ₛs _) = z<ₛs
trans ⦃ Transitive<ₛ ⦄ (s<ₛs a<b) (s<ₛs b<c) = s<ₛs (trans a<b b<c)

Decidable<ₛ {a = zero} {zero} = false (λ ())
Decidable<ₛ {a = zero} {suc n} = true z<ₛs
Decidable<ₛ {a = suc m} {zero} = false (λ ())
Decidable<ₛ {a = suc m} {suc n} with decide (m <ₛ n)
Decidable<ₛ {a = suc m} {suc n} | true n<m = true (s<ₛs n<m)
Decidable<ₛ {a = suc m} {suc n} | false ¬n<m = false λ m<n → ¬n<m (s<s→-<- m<n)
  
rel-preserv ⦃ Relating-suc-<ₛ ⦄ = s<ₛs

UniversalPostfix.postfix Postfix-suc-<ₛ zero = z<ₛs
UniversalPostfix.postfix Postfix-suc-<ₛ (suc x) = s<ₛs $ postfix suc x

rel-preserv ⦃ Relating-maxFinℕ ⦄ {ℕ.zero}{ℕ.zero} (_ , 0≠0) =
  ⊥-recursion _ $ 0≠0 $ Id.refl 0
rel-preserv ⦃ Relating-maxFinℕ ⦄ {ℕ.zero}{ℕ.suc _} _ = z<ₛs
rel-preserv ⦃ Relating-maxFinℕ ⦄ {ℕ.suc a}{ℕ.suc b} a+1<b+1 =
  s<ₛs $ rel-preserv ⦃ Relating-maxFinℕ ⦄ $ ℕ.s<s→-<- a+1<b+1

rel-preserv ⦃ Relating-toℕ ⦄ {_}{suc a} z<ₛs = z<s (toℕ a)
rel-preserv ⦃ Relating-toℕ ⦄ (s<ₛs rab) = s<s (rel-preserv rab)

infix 35 _≤ₛ_
_≤ₛ_ : Finℕ n → Finℕ n → 𝒰₀ ᵖ
a ≤ₛ b = a == b ∨ a <ₛ b

instance
  Reflexive≤ₛ : Reflexive (_≤ₛ_ {n})
  Transitive≤ₛ : Transitive (_≤ₛ_ {n})
  Antisym≤ₛ : Antisymmetric (_≤ₛ_ {n})
  Relating-suc-≤ₛ : Relating suc (_≤ₛ_ {n}) (_≤ₛ_ {ℕ.suc n})
  Relating-cap : Relating (λ m → toℕ (cap m n)) _≤_ _≤_

refl ⦃ Reflexive≤ₛ ⦄ a = ∨left (refl a)
  
trans ⦃ Transitive≤ₛ ⦄ (∨left (Id.refl a)) a≤b = a≤b
trans ⦃ Transitive≤ₛ ⦄ (∨right a<b) (∨left (Id.refl b)) = ∨right a<b
trans ⦃ Transitive≤ₛ ⦄ (∨right a<b) (∨right b<c) = ∨right $ trans a<b b<c
  
antisym ⦃ Antisym≤ₛ ⦄ (∨left a==b) _ = a==b
antisym ⦃ Antisym≤ₛ ⦄ (∨right _) (∨left b==a) = sym b==a
antisym ⦃ Antisym≤ₛ ⦄ (∨right a<b) (∨right b<a) = ⊥-recursion _ (asym a<b b<a)

rel-preserv ⦃ Relating-suc-≤ₛ ⦄ (∨left (Id.refl x)) = refl (suc x)
rel-preserv ⦃ Relating-suc-≤ₛ ⦄ (∨right a<b) = ∨right (ap suc a<b)

rel-preserv ⦃ Relating-cap {n} ⦄ {m} {m'} m≤m' = 
  proof toℕ $' cap m n
    === toℕ $' toFinℕ (min m n) (p m)
      :by: Id.refl _
    === min m n
      :by: toℕ-toFinℕ $ p m
    〉 _≤_  〉 min m' n
      :by: rel-preserv m≤m'
    === toℕ $' toFinℕ (min m' n) (p m')
      :by: sym {R = _==_} $ toℕ-toFinℕ $ p m'
    === toℕ $' cap m' n
      :by: Id.refl _
  qed
  where open import Function renaming (_$_ to _$'_)
        p = λ m → ap ℕ.suc $ prefix (λ — → min — n) m


