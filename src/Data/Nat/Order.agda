{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Order where

open import PropUniverses hiding (_⊔_)
open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern

open import Proposition.Identity
  renaming (refl to Id-refl) using (_==_; ap)
open import Proposition.Decidable.Definition
open import Function hiding (_$_; _~_)
open import Relation.Binary
open import Operation.Binary
open import Logic
open import Proof
open import Function.Proof

data _≤_ : BinRel 𝒰₀ ℕ where
  z≤_ : ∀ m → 0 ≤ m
  s≤s : (p : n ≤ m) → n +1 ≤ m +1

infix 35 _≤_ _<_ _≥_ _>_
_<_ _≥_ _>_ suc_==_ : BinRel 𝒰₀ ℕ

_≥_ = flip _≤_
m < n = m ≤ n ∧ m ≠ n
_>_ = flip _<_

z<s_ : ∀ m → 0 < m +1
z<s m = z≤ (m +1) , λ ()

suc m == n = m +1 == n
_rtc-≤_ = refl-trans-close suc_==_

instance
  Relating-suc-≤-single : Relating suc suc_==_ suc_==_

rel-preserv ⦃ Relating-suc-≤-single ⦄ (Id-refl (m +1)) = refl (m +2)

open import Data.Nat.Arithmetic

private
  ∃+ : BinRel 𝒰₀ ℕ

∃+ n m = ∃ λ k → k + n == m

rtc-≤-↔-∃+ : m rtc-≤ n ↔ ∃+ m n
rtc-≤-↔-∃+ = forw-dir , λ { (k , p) → back-dir k p}
  where open MakeComposable _rtc-≤_
        forw-dir : (p : m rtc-≤ n) → ∃ λ k → k + m == n
        forw-dir (rfl m) = 0 , refl m
        forw-dir (step {b = b +1} (Id-refl _) b+1≤n) with forw-dir b+1≤n
        forw-dir (step {_} {b +1} (Id-refl _) b+1≤n) | k , Id-refl _ =
          k +1 , sym $ +-suc k b
        back-dir : ∀ k (p : k + m == n) → m rtc-≤ n
        back-dir zero (Id-refl m) = refl m
        back-dir {m = m}{n} (k +1) p =
          proof m
            〉 _rtc-≤_ 〉 k + m    :by: back-dir k $ refl (k + m)
            〉 suc_==_ 〉 k + m +1 :by: refl (k + m +1) 
            〉 _==_ 〉 n       :by: p
          qed

open import Logic.Proof

≤-↔-∃+ : ∀ {n m} → n ≤ m ↔ ∃+ n m
⟶ ≤-↔-∃+ (z≤ m) = m , left-unit m
⟶ ≤-↔-∃+ (s≤s p) with ⟶ ≤-↔-∃+ p
⟶ ≤-↔-∃+ (s≤s p) | k , Id-refl .(k + _) = k , +-suc k _
⟵ ≤-↔-∃+ (zero , Id-refl zero) = z≤ 0
⟵ ≤-↔-∃+ (zero , Id-refl (m +1)) =
  s≤s $ ⟵ (≤-↔-∃+ {m}{m}) (0 , refl m)
⟵ (≤-↔-∃+ {zero}) (k +1 , Id-refl .(k + 0 +1)) = z≤ k + 0 +1
⟵ (≤-↔-∃+ {n +1}) (k +1 , Id-refl .(k + (n +1) +1)) =
  s≤s $ ⟵ (≤-↔-∃+ {n}) (k +1 , sym $ +-suc k n)

instance
  ≤-⊆-rtc-≤ : _≤_ ⊆ _rtc-≤_
  rtc-≤-⊆-≤ : _rtc-≤_ ⊆ _≤_

≤-↔-rtc-≤ : ∀ {n m} → n ≤ m ↔ n rtc-≤ m
≤-↔-rtc-≤ {n} {m} =
  proof n ≤ m
    〉 _↔_ 〉 ∃+ n m    :by: ≤-↔-∃+
    〉 _↔_ 〉 n rtc-≤ m :by: sym rtc-≤-↔-∃+
  qed

≤-⊆-rtc-≤ = ↔-→-⊆ ≤-↔-rtc-≤
rtc-≤-⊆-≤ = ↔-→-⊇ ≤-↔-rtc-≤

open import
  Relation.Binary.ReflexiveTransitiveClosure.Transfer _≤_ suc_==_
  public

module Composable-≤ where
  open MakeTransComposable _≤_ public

instance
  Antisym≤ : Antisymmetric _≤_
  Connex≤ : Connex _≤_
  Prefix-pred-≤ : UniversalPrefix pred _≤_
  Relating-pred-≤ : Relating pred _≤_ _≤_
  Decidable≤ : ∀ {m n} → Decidable (m ≤ n)

antisym ⦃ Antisym≤ ⦄ (z≤ 0) (z≤ 0) = refl 0
antisym ⦃ Antisym≤ ⦄ (s≤s p) (s≤s q) = ap suc $ antisym p q

total ⦃ Connex≤ ⦄ zero y = ∨left $ z≤ y
total ⦃ Connex≤ ⦄ (x +1) zero = ∨right $ z≤ x +1
total ⦃ Connex≤ ⦄ (x +1) (y +1) = ∨[ s≤s ⸴ s≤s ] (total x y)

UniversalPrefix.prefix Prefix-pred-≤ zero = refl 0
UniversalPrefix.prefix Prefix-pred-≤ (x +1) =
  subrel ⦃ ~-⊇ ⦄ $ subrel $ Id-refl (x +1)

rel-preserv ⦃ Relating-pred-≤ ⦄ {zero} {zero} rab = refl 0
rel-preserv ⦃ Relating-pred-≤ ⦄ {zero} {b +1} rab = z≤ b
rel-preserv ⦃ Relating-pred-≤ ⦄ {a +1} {b +1} (s≤s a≤b) = a≤b

Decidable≤ {zero} {n} = true (z≤ n)
Decidable≤ {m +1} {zero} = false λ ()
Decidable≤ {m +1} {n +1} with Decidable≤ {m} {n}
Decidable≤ {m +1} {n +1} | true p = true (s≤s p)
Decidable≤ {m +1} {n +1} | false ¬p = false (λ p' → ¬p $ ap pred p')

-≤s : (n≤m : n ≤ m) → n ≤ m +1
-≤s (z≤ m) = z≤ m +1
-≤s (s≤s n≤m) = s≤s $ -≤s n≤m

-≤self+1 : ∀ m → m ≤ m +1
-≤self+1 m = -≤s $ refl m

instance
  Irreflexive< : Irreflexive _<_
  Asym< : Asymmetric _<_
  Transitive< : Transitive _<_

irrefl ⦃ Irreflexive< ⦄ m (_ , m≠m) = m≠m $ refl m

asym ⦃ Asym< ⦄ (x≤y , x≠y) (y≤x , _) = x≠y $ antisym x≤y y≤x

trans ⦃ Transitive< ⦄ (x≤y , x≠y) (y≤z , y≠z) =
  trans x≤y y≤z , trans≠ (x≤y , x≠y) y≤z
  where trans≠ : (p : n < m)(q : m ≤ k) → n ≠ k
        trans≠ (z≤ 0 , 0≠0) (z≤ m) _ = 0≠0 $ refl 0
        trans≠ (s≤s n≤m , n+1≠m+1) (s≤s q) r =
          trans≠ (n≤m , λ n==m → n+1≠m+1 $ ap suc n==m) q $ ap pred r

s<s : (n<m : n < m) → n +1 < m +1
s<s (n≤m , n≠m) = s≤s n≤m , ap suc n≠m

-<-↔s≤- : n < m ↔ n +1 ≤ m
⟶ -<-↔s≤- (z≤ zero , 0≠0) = ⊥-recursion _ $ 0≠0 $ refl 0
⟶ -<-↔s≤- (z≤ (m +1) , _) = s≤s $ z≤ m
⟶ -<-↔s≤- (s≤s p , n+1≠m+1) =
  s≤s $ ⟶ -<-↔s≤- (p , λ n==m → n+1≠m+1 $ ap suc n==m)
⟵ -<-↔s≤- (s≤s (z≤ m)) = z≤ m +1 , λ ()
⟵ -<-↔s≤- (s≤s (s≤s q)) = s<s $ ⟵ -<-↔s≤- (s≤s q)

-<s : (n<m : n < m) → n < m +1
-<s n<m = ⟵ -<-↔s≤- $ -≤s $ ⟶ -<-↔s≤- n<m

-<self+1 : ∀ m → m < m +1
-<self+1 m = ⟵ -<-↔s≤- $ refl (m +1)

s<s→-<- : (n+1<m+1 : n +1 < m +1) → n < m
s<s→-<- n+1<m+1 = ⟵ -<-↔s≤- $ ap pred $ ⟶ -<-↔s≤- n+1<m+1

-- -<s↔¬->- : ∀ {a b} → a < suc b ↔ ¬ a > b
-- ⟶ (-<s↔¬->- {suc a} {zero}) (s<s ())
-- ⟶ -<s↔¬->- (s<s a<sb) (s<s b<a) = ⟶ -<s↔¬->- a<sb b<a
-- ⟵ (-<s↔¬->- {zero}) q = z<s
-- ⟵ (-<s↔¬->- {suc a} {zero}) q = ⊥-recursion (suc a < 1) (q z<s)
-- ⟵ (-<s↔¬->- {suc a} {suc b}) q = ap suc $ ⟵ -<s↔¬->- $ λ a>b → q (s<s a>b )

-- <→== : ∀ {n m}
--   (p : n < suc m)
--   (q : ¬ n < m)
--   → ---------------
--   n == m
-- <→== {n} {m} p q with compare n _<_ m
-- <→== {n} {m} p q | lt p₁ = ⊥-recursion (n == m) (q p₁)
-- <→== {n} {m} p q | eq p₁ = p₁
-- <→== {n} {m} p q | gt p₁ = ⊥-recursion (n == m) (⟶ -<s↔¬->- p p₁)

infix 35 _≤ₜ_ _<ₜ_
_≤ₜ_ _<ₜ_ : BinRel 𝒰₀ ℕ
0 ≤ₜ _ = ⊤
_ +1 ≤ₜ 0 = ⊥
n +1 ≤ₜ m +1 = n ≤ₜ m

n <ₜ m = n +1 ≤ₜ m

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
min≤ (m +1) zero = z≤ (m +1)
min≤ (m +1) (n +1) = s≤s $ min≤ m n

≤max : ∀ m n → m ≤ m ⊔ n
≤max zero n = z≤ n
≤max (m +1) zero = refl (m +1)
≤max (m +1) (n +1) = s≤s $ ≤max m n 

≤→min== : (p : n ≤ m) → n ⊓ m == n
≤→min== (z≤ m) = refl 0
≤→min== (s≤s p) = ap suc $ ≤→min== p

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
--           minimality ⦃ minimal ⦄ {x} (∨left (Id-refl y)) = {!!}
--           minimality ⦃ minimal ⦄ {x} (∨right q) = {!!}

