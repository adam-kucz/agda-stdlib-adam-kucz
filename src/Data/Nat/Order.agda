{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Order where

open import PropUniverses hiding (_⊔_)
open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

open import Proposition.Identity renaming (Idₚ to Id) using (_==_; ap)
open import Proposition.Decidable.Definition
open import Relation.Binary.Property
open import Operation.Binary
open import Logic
open import Function.Proof

open import Proposition.Function using (_$_; _∘_)

infix 35 _<_ _>_
data _<_ : (m n : ℕ) → 𝒰₀ ᵖ where
  z<s : ∀ {n} → 0 < suc n
  s<s : ∀ {m n} → n < m → suc n < suc m

_>_ : (m n : ℕ) → 𝒰₀ ᵖ
a > b = b < a

-<s : ∀ {m n} → (n<m : n < m) → n < suc m
-<s z<s = z<s
-<s (s<s n<m) = s<s (-<s n<m)

s<s→-<- : ∀ {m n} → (p : suc n < suc m) → n < m
s<s→-<- (s<s p) = p

-≮0 : ∀ {n} → ¬ n < 0
-≮0 ()

instance
  Irreflexive< : Irreflexive _<_
  irrefl ⦃ Irreflexive< ⦄ 0 ()
  irrefl ⦃ Irreflexive< ⦄ (suc n) sn<sn = irrefl n (s<s→-<- sn<sn)

  Asym< : Asymmetric _<_
  asym ⦃ Asym< ⦄ z<s ()
  asym ⦃ Asym< ⦄ (s<s a<b) (s<s b<a) = asym b<a a<b

  Transitive< : Transitive _<_
  trans ⦃ Transitive< ⦄ z<s (s<s _) = z<s
  trans ⦃ Transitive< ⦄ (s<s a<b) (s<s b<c) = s<s (trans a<b b<c)

  Decidable< : ∀ {m n} → Decidable (m < n)
  Decidable< {zero} {zero} = false (λ ())
  Decidable< {zero} {suc n} = true z<s
  Decidable< {suc m} {zero} = false (λ ())
  Decidable< {suc m} {suc n} with decide (m < n)
  Decidable< {suc m} {suc n} | true n<m = true (s<s n<m)
  Decidable< {suc m} {suc n} | false ¬n<m = false λ m<n → ¬n<m (s<s→-<- m<n)
  
  Relating-suc-< : Relating suc _<_ _<_
  rel-preserv ⦃ Relating-suc-< ⦄ = s<s

  Postfix-suc-< : UniversalPostfix suc _<_
  UniversalPostfix.postfix Postfix-suc-< zero = z<s
  UniversalPostfix.postfix Postfix-suc-< (suc x) = s<s $ postfix suc x

infix 35 _≤_ _≥_
_≤_ _≥_ : (m n : ℕ) → 𝒰₀ ᵖ
a ≤ b = a == b ∨ a < b
a ≥ b = b ≤ a

instance
  Reflexive≤ : Reflexive _≤_
  refl ⦃ Reflexive≤ ⦄ a = ∨left (refl a)
  
  Transitive≤ : Transitive _≤_
  trans ⦃ Transitive≤ ⦄ (∨left (Id.refl a)) a≤b = a≤b
  trans ⦃ Transitive≤ ⦄ (∨right a<b) (∨left (Id.refl b)) = ∨right a<b
  trans ⦃ Transitive≤ ⦄ (∨right a<b) (∨right b<c) = ∨right $ trans a<b b<c
  
  Antisym≤ : Antisymmetric _≤_
  antisym ⦃ Antisym≤ ⦄ (∨left a==b) _ = a==b
  antisym ⦃ Antisym≤ ⦄ (∨right _) (∨left b==a) = sym b==a
  antisym ⦃ Antisym≤ ⦄ (∨right a<b) (∨right b<a) = ⊥-recursion _ (asym a<b b<a)

  Relating-suc-≤ : Relating suc _≤_ _≤_
  rel-preserv ⦃ Relating-suc-≤ ⦄ (∨left (Id.refl x)) = refl (suc x)
  rel-preserv ⦃ Relating-suc-≤ ⦄ (∨right a<b) = ∨right (ap suc a<b)

  Relating-pred-≤ : Relating pred _≤_ _≤_
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨left (Id.refl x)) = refl (pred x)
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (z<s {0})) = ∨left (refl 0)
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (z<s {suc n})) = ∨right z<s
  rel-preserv ⦃ Relating-pred-≤ ⦄ (∨right (s<s q)) = ∨right q

  Postfix-suc-≤ : UniversalPostfix suc _≤_
  UniversalPostfix.postfix Postfix-suc-≤ x = ∨right $ postfix suc x

  Prefix-pred-≤ : UniversalPrefix pred _≤_
  UniversalPrefix.prefix Prefix-pred-≤ 0 = ∨left (refl 0)
  UniversalPrefix.prefix Prefix-pred-≤ (suc x) = postfix suc x

-≤-↔-<s : ∀ {a b} → a ≤ b ↔ a < suc b
⟶ -≤-↔-<s (∨left (Id.refl x)) = postfix suc x
⟶ -≤-↔-<s (∨right a<b) = -<s a<b
⟵ -≤-↔-<s (s<s (s<s a<b)) = ap suc $ ⟵ -≤-↔-<s $ s<s a<b
⟵ -≤-↔-<s (s<s (z<s {0})) = ap suc $ refl 0
⟵ -≤-↔-<s (s<s (z<s {suc n})) = ap suc $ ∨right z<s
⟵ -≤-↔-<s (z<s {0}) = refl 0
⟵ -≤-↔-<s (z<s {suc n}) = ∨right z<s

open import Proposition.Comparable

instance
  Comparableℕ : {x y : ℕ} → Comparable _<_ x y
  Comparableℕ {zero} {zero} = eq (refl 0)
  Comparableℕ {zero} {suc y} = lt z<s
  Comparableℕ {suc x} {zero} = gt z<s
  Comparableℕ {suc x} {suc y} with compare x _<_ y
  Comparableℕ {suc x} {suc y} | lt p = lt (ap suc p)
  Comparableℕ {suc x} {suc y} | eq p = eq (ap suc p)
  Comparableℕ {suc x} {suc y} | gt p = gt (ap suc p)

-<s↔¬->- : ∀ {a b} → a < suc b ↔ ¬ a > b
⟶ (-<s↔¬->- {suc a} {zero}) (s<s ())
⟶ -<s↔¬->- (s<s a<sb) (s<s b<a) = ⟶ -<s↔¬->- a<sb b<a
⟵ (-<s↔¬->- {zero}) q = z<s
⟵ (-<s↔¬->- {suc a} {zero}) q = ⊥-recursion (suc a < 1) (q z<s)
⟵ (-<s↔¬->- {suc a} {suc b}) q = ap suc $ ⟵ -<s↔¬->- $ λ a>b → q (s<s a>b )

<→== : ∀ {n m}
  (p : n < suc m)
  (q : ¬ n < m)
  → ---------------
  n == m
<→== {n} {m} p q with compare n _<_ m
<→== {n} {m} p q | lt p₁ = ⊥-recursion (n == m) (q p₁)
<→== {n} {m} p q | eq p₁ = p₁
<→== {n} {m} p q | gt p₁ = ⊥-recursion (n == m) (⟶ -<s↔¬->- p p₁)

infix 35 _<ₜ_
_<ₜ_ : (n m : ℕ) → 𝒰₀ ᵖ
_ <ₜ 0 = ⊥
0 <ₜ suc _ = ⊤
suc n <ₜ suc m = n <ₜ m

infixl 120 _⊓_ _⊔_
_⊓_ min : (x y : ℕ) → ℕ
zero ⊓ _ = zero
suc _ ⊓ zero = zero
suc x ⊓ suc y = suc (x ⊓ y)

_⊔_ max : (x y : ℕ) → ℕ
zero ⊔ y = y
suc x ⊔ zero = suc x
suc x ⊔ suc y = suc (x ⊔ y)

min = _⊓_
max = _⊔_

instance
  min-comm : Commutative _⊓_
  min-assoc : Associative _⊓_
  min-0-left : 0 IsLeftZeroOf _⊓_
  min-0-right : 0 IsRightZeroOf _⊓_
  max-comm : Commutative _⊔_
  max-assoc : Associative _⊔_
  max-0-left : 0 IsLeftUnitOf _⊔_
  max-0-right : 0 IsRightUnitOf _⊔_

comm ⦃ min-comm ⦄ zero zero = refl 0
comm ⦃ min-comm ⦄ zero (suc b) = refl 0
comm ⦃ min-comm ⦄ (suc a) zero = refl 0
comm ⦃ min-comm ⦄ (suc a) (suc b) = ap suc $ comm a b
assoc ⦃ min-assoc ⦄ zero y z = refl 0
assoc ⦃ min-assoc ⦄ (x +1) zero z = refl 0
assoc ⦃ min-assoc ⦄ (x +1) (y +1) zero = refl 0
assoc ⦃ min-assoc ⦄ (x +1) (y +1) (z +1) = ap suc $ assoc x y z
left-zero ⦃ min-0-left ⦄ _ = refl 0
right-zero ⦃ min-0-right ⦄ zero = refl 0
right-zero ⦃ min-0-right ⦄ (_ +1) = refl 0

comm ⦃ max-comm ⦄ zero zero = refl 0
comm ⦃ max-comm ⦄ zero (suc y) = refl (suc y)
comm ⦃ max-comm ⦄ (suc x) zero = refl (suc x)
comm ⦃ max-comm ⦄ (suc x) (suc y) = ap suc $ comm x y
assoc ⦃ max-assoc ⦄ zero y z = refl (y ⊔ z)
assoc ⦃ max-assoc ⦄ (x +1) zero z = refl (x +1 ⊔ z)
assoc ⦃ max-assoc ⦄ (x +1) (y +1) zero = refl ((x ⊔ y) +1)
assoc ⦃ max-assoc ⦄ (x +1) (y +1) (z +1) = ap suc $ assoc x y z
left-unit ⦃ max-0-left ⦄ y = refl y
right-unit ⦃ max-0-right ⦄ zero = refl 0
right-unit ⦃ max-0-right ⦄ (y +1) = refl (y +1)

min== : ∀ m n → m ⊓ n == m ∨ m ⊓ n == n
min== zero n = ∨left (refl 0)
min== (suc _) zero = ∨right (refl 0)
min== (suc m) (suc n) with min== m n
min== (suc m) (suc n) | ∨left min-m-n==m = ∨left $ ap suc min-m-n==m
min== (suc m) (suc n) | ∨right min-m-n==n = ∨right $ ap suc min-m-n==n

min≤ : ∀ m n → m ⊓ n ≤ m
min≤ zero n = refl 0
min≤ (m +1) zero = ∨right z<s
min≤ (m +1) (n +1) = ap suc (min≤ m n)

≤max : ∀ m n → m ≤ m ⊔ n
≤max zero zero = refl 0
≤max zero (n +1) = ∨right z<s
≤max (m +1) zero = refl (m +1)
≤max (m +1) (n +1) = ap suc (≤max m n)

≤→min== : ∀ {m n} → (p : n ≤ m) → n ⊓ m == n
≤→min== (∨left (Id.refl n)) = ∨-contract (min== n n)
≤→min== (∨right z<s) = refl 0
≤→min== (∨right (s<s n<m)) = ap suc $ ≤→min== $ ∨right n<m

-- <induction :
--   {A : (n : ℕ) → 𝒰 ᵖ}
--   (f : (n : ℕ) → ℕ)
--   (p : UniversalPrefix f _<_)
--   → -------------------
--   (n : ℕ) → B
-- <induction = {!!}

-- least-elem :
--   (𝐴 : (n : ℕ) → 𝒰 ᵖ)
--   ⦃ _ : ∀ {n} → Decidable (𝐴 n) ⦄
--   (e : Subset ℕ 𝐴)
--   → --------------------
--   Subset ℕ 𝐴
-- least-elem 𝐴 e = smallest e
--   where open import Proposition.Sum
--         open import Data.Maybe
--         smaller : (n : ℕ)
--           → --------------------------------------------------
--           Maybe (Σₚ λ (e' : Subset ℕ 𝐴) → elem e' < n)
--         smaller zero = nothing
--         smaller (suc n) with decide (𝐴 n)
--         smaller (suc n) | true p = just (n , p , postfix suc n)
--         smaller (suc n) | false _ with smaller n
--         smaller (suc n) | false _ | nothing = nothing
--         smaller (suc n) | false _ | just (m , m<n) =
--           just (m , trans m<n $ postfix suc n)
--         smallest = {!!}

-- instance
--   WellFounded≤ : WellFounded _≤_ least-elem
--   well-founded ⦃ WellFounded≤ ⦄ 𝐴 (elem , prop) = minimal
--     where minimal : Minimal (on-elems _≤_) (least-elem 𝐴 (elem , prop))
--           minimality ⦃ minimal ⦄ {x} (∨left (Id.refl y)) = {!!}
--           minimality ⦃ minimal ⦄ {x} (∨right q) = {!!}

