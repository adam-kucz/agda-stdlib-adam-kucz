{-# OPTIONS --exact-split --safe --prop #-}
module Data.FinNat.Arithmetic where

open import Data.Nat
open import Data.FinNat.Definition
open import Data.FinNat.Property
open import Function using (_∘_) renaming (_$_ to _$'_)
open import Logic

open import Relation.Binary.Property
open import Operation.Binary.Property
open import Structure.Monoid
open import Structure.Hemiring hiding (zero; _+_; _*_)

open import Proof
open import Function.Proof
open import Function.Property using (inj)
open import Data.Nat.Proof
open import Proposition.Decidable using (decide; true; false)
open import Proposition.Identity renaming (Idₚ to Id) using (_==_)

-- return n if n fits in Finℕ (m + 1) [i.e. when n ≤ m]
-- otherwise return the largest element of Finℕ (m + 1)
cap : (m n : ℕ) → Finℕ (suc m)
cap m n = toFinℕ {suc m} (min m n) (ap suc $ prefix (λ — → min — n) m)

-- instance
--   Relating-maxFinℕ : Relating (λ n → maxFinℕ {n}) _<_ _<ₛ_
--   rel-preserv ⦃ Relating-maxFinℕ ⦄ z<s = z<ₛs
--   rel-preserv ⦃ Relating-maxFinℕ ⦄ (s<s rab) = s<ₛs (rel-preserv rab)

  -- Relating-suc : Relating (suc {n}) _<ₛ_ _<ₛ_
  -- rel-preserv ⦃ Relating-suc ⦄ = s<ₛs

  -- Relating-toℕ : Relating (toℕ {n}) _<ₛ_ _<_
  -- rel-preserv ⦃ Relating-toℕ ⦄ z<ₛs = z<s
  -- rel-preserv ⦃ Relating-toℕ ⦄ (s<ₛs rab) = s<s (rel-preserv rab)

-- instance
--   Relating-cap : Relating (λ m → toℕ $ cap m n) _≤_ _≤_
--   rel-preserv ⦃ Relating-cap {n} ⦄ {m} {m'} m≤m' = 
--     proof toℕ $ cap m n
--       〉 _==_ 〉 toℕ $ toFinℕ (min m n) min<s :by: refl
--       〉 _==_ 〉 min m n :by: toℕ-toFinℕ min<s
--       〉 _≤_ 〉 min m' n :by: rel-preserv m≤m'
--       〉 _==_ 〉 toℕ $ toFinℕ (min m' n) min<s :by: ← toℕ-toFinℕ min<s
--       〉 _==_ 〉 toℕ $ cap m' n :by: refl
--     qed

cap== : ∀ {l m n} → m == n → cap l m == cap l n
cap== {l} (Id.refl m) = Id.refl (cap l m)

cap-n-zero==zero : ∀ {n} → cap n zero == Finℕ.zero {n}
cap-n-zero==zero {n} = 
  proof cap n zero
    === toFinℕ (min n 0) _
      :by: Id.refl (cap n zero)
    === toFinℕ zero (ap suc $ z≤ n)
      :by: subrel $
           toFinℕ== (right-zero n)(Id.refl (n +1))
                     (ap suc $ prefix (λ — → min — 0) n)
    === zero
      :by: Id.refl zero
  qed

cap-suc== :
  ∀ {l m n} →
  (eq : cap (suc l) m == cap (suc l) n)
  → ------------------------------------
  cap l m == cap l n
cap-suc== {l} {zero} {zero} eq = refl (cap l 0)
cap-suc== {zero} {suc m} {suc n} eq = refl zero
cap-suc== {suc l} {suc m} {suc n} eq =
  ap Finℕ.suc $ cap-suc== {l} {m} {n} (inj $ subrel eq)
  
cap-toℕ : ∀ {n} {a : Finℕ (suc n)} → cap n (toℕ a) == a
cap-toℕ {zero} {zero} = refl 0
cap-toℕ {suc n} {zero} = refl 0
cap-toℕ {suc n} {suc a} = ap Finℕ.suc $ cap-toℕ {n} {a}

toℕ-cap-fit : ∀ {m n} (n<sm : n ≤ m) → toℕ (cap m n) == n
toℕ-cap-fit {zero} {zero} _ = refl 0
toℕ-cap-fit {suc _} {zero} _ = refl 0
toℕ-cap-fit {suc m} {suc n} (s≤s n≤m) = ap suc $ toℕ-cap-fit n≤m

toℕ-cap-overflow : ∀ {m n} (¬n≤m : ¬ n ≤ m) → toℕ (cap m n) == m
toℕ-cap-overflow {m} {zero} ¬n≤m = ⊥-recursion _ $ ¬n≤m $ z≤ m
toℕ-cap-overflow {zero} {suc _} _ = refl 0
toℕ-cap-overflow {suc m} {suc n} ¬n≤m =
  ap suc $ toℕ-cap-overflow λ n≤m → ¬n≤m (s≤s n≤m)

cap-thm : ∀ {m n}
  (f : ℕ → ℕ)
  (x≤fx : ∀ x → x ≤ f x)
  → --------------------------------
  cap m (f (toℕ (cap m n))) == cap m (f n)
cap-thm {zero} {zero} _ _ = refl 0
cap-thm {suc m} {zero} f _ = refl (cap (suc m) (f 0))
cap-thm {zero} {suc _} _ _ = refl 0
cap-thm {suc m} {suc n} _ _ with decide (n ≤ m)
cap-thm {suc m} {suc n} f _ | true n≤m =
  ap (cap (suc m) ∘ f ∘ suc) $ toℕ-cap-fit n≤m
cap-thm {suc m} {suc n} f x≤fx | false ¬n≤m =
  proof cap (suc m) ∘ f ∘ suc ∘ toℕ $' cap m n
    === cap (suc m) ∘ f ∘ suc $' m
      :by: ap (cap (suc m) ∘ f ∘ suc) $ toℕ-cap-overflow ¬n≤m
    === toFinℕ (min (suc m) (f $' suc m)) _
      :by: Id.refl _
    === toFinℕ (min (suc m) (f $' suc n)) _
      :by: subrel $ toFinℕ== min-sm-fsn==min-sm-fsm (Id.refl (m +2)) _
    === cap (suc m) ∘ f ∘ suc $' n
      :by: Id.refl (cap (suc m) (f $' suc n))
  qed
  where sm≤fsn : suc m ≤ f (suc n)
        min-sm-fsn==min-sm-fsm :
          min (suc m) (f (suc m)) == min (suc m) (f (suc n))
        min-sm-fsn==min-sm-fsm =
          proof min (suc m) (f (suc m))
            === suc m                   :by: ≤→min== $ x≤fx (suc m)
            === min (suc m) (f (suc n)) :by: sym $ ≤→min== sm≤fsn
          qed
        sm≤fsn with total m n
        sm≤fsn | ∨left m≤n =
          proof suc m
            〉 _≤_ 〉 suc n     :by: ap suc m≤n
            〉 _≤_ 〉 f (suc n) :by: x≤fx (suc n)
          qed
        sm≤fsn | ∨right n≤m = ⊥-recursion _ $ ¬n≤m n≤m

infixl 20 _+ₛ_
_+ₛ_ : ∀ {n} (x : Finℕ n) (y : Finℕ n) → Finℕ n
_+ₛ_ {suc n} x y = cap n $' toℕ x + toℕ y

infixl 21 _*ₛ_
_*ₛ_ : ∀ {n} (x : Finℕ n) (y : Finℕ n) → Finℕ n
_*ₛ_ {suc n} x y = cap n $' toℕ x * toℕ y

instance
  CommutativeFinℕ+ : ∀ {n} → Commutative (_+ₛ_ {n})
  comm ⦃ CommutativeFinℕ+ {suc n} ⦄ a b = ap (cap n) $ comm (toℕ a) (toℕ b)

  assoc+ₛ : ∀ {n} → Associative (_+ₛ_ {n})
  assoc ⦃ assoc+ₛ {suc n} ⦄ a b c = 
    proof a +ₛ (b +ₛ c)
      〉 _==_ 〉 cap n $' toℕ a + toℕ (cap n $' toℕ b + toℕ c)
        :by: refl (a +ₛ (b +ₛ c))
      〉 _==_ 〉 cap n $' toℕ a + (toℕ b + toℕ c)
        :by: cap-thm (toℕ a +_) $ postfix (toℕ a +_)
      〉 _==_ 〉 cap n $' (toℕ a + toℕ b) + toℕ c
        :by: ap (cap n) $ assoc (toℕ a) (toℕ b) (toℕ c)
      〉 _==_ 〉 cap n $' toℕ (cap n $' toℕ a + toℕ b) + toℕ c
        :by: sym $
               cap-thm (_+ toℕ c) $
               postfix (_+ toℕ c)
      〉 _==_ 〉 a +ₛ b +ₛ c :by: refl (a +ₛ b +ₛ c)
    qed
  
  0-+ₛ : ∀ {n} → 0 IsLeftUnitOf (_+ₛ_ {suc n})
  left-unit ⦃ 0-+ₛ ⦄ a = cap-toℕ

  +ₛ-0 : ∀ {n} → 0 IsRightUnitOf (_+ₛ_ {suc n})
  +ₛ-0 = right-unit-of-commutative-left-unit 0 _+ₛ_
  
  CommutativeFinℕ* : ∀ {n} → Commutative (_*ₛ_ {n})
  comm ⦃ CommutativeFinℕ* {suc n} ⦄ a b = ap (cap n) $ comm (toℕ a) (toℕ b)

  assoc*ₛ : ∀ {n} → Associative (_*ₛ_ {n})
  assoc ⦃ assoc*ₛ {suc n} ⦄ zero b c =
    proof cap n zero
      〉 _==_ 〉 cap n (toℕ (Finℕ.zero {n}) * toℕ c) :by: refl (cap n zero)
      〉 _==_ 〉 cap n (toℕ (cap n zero) * toℕ c)
        :by: ap (λ – → cap n (toℕ – * toℕ c)) $ sym $ cap-n-zero==zero {n}
    qed
    where 
  assoc ⦃ assoc*ₛ {suc n} ⦄ (suc a) b zero = ap (cap n) $
    (proof toℕ (suc a) * toℕ (cap n (toℕ b * 0))
      〉 _==_ 〉 toℕ (suc a) * toℕ (cap n 0)
        :by: ap (λ – → toℕ (suc a) * toℕ (cap n –)) $ right-zero (toℕ b)
      〉 _==_ 〉 toℕ (suc a) * 0
        :by: ap (λ – → toℕ (suc a) * toℕ –) $ cap-n-zero==zero {n}
      〉 _==_ 〉 0                    :by: right-zero (toℕ $' suc a)
      〉 _==_ 〉 toℕ (suc a *ₛ b) * 0 :by: sym $ right-zero (toℕ (suc a *ₛ b))
    qed)
  assoc ⦃ assoc*ₛ {suc n} ⦄ (suc a) b (suc c) =
    proof suc a *ₛ (b *ₛ suc c)
      〉 _==_ 〉 cap n $' suc (toℕ a) * toℕ (cap n $' toℕ b * suc (toℕ c))
        :by: refl (suc a *ₛ (b *ₛ suc c))
      〉 _==_ 〉 cap n $' suc (toℕ a) * (toℕ b * suc (toℕ c))
        :by: cap-thm (suc (toℕ a) *_) $
             postfix (suc (toℕ a) *_) ⦃ Postfix-*-left-≤ {toℕ a} ⦄
      〉 _==_ 〉 cap n $' (suc (toℕ a) * toℕ b) * suc (toℕ c)
        :by: ap (cap n) $ assoc (suc $' toℕ a) (toℕ b) (suc $' toℕ c)
      〉 _==_ 〉 cap n $' toℕ (cap n $' suc (toℕ a) * toℕ b) * suc (toℕ c)
        :by: sym $
               cap-thm (_* suc (toℕ c)) $
               postfix (_* suc (toℕ c))
      〉 _==_ 〉 suc a *ₛ b *ₛ suc c
        :by: refl (suc a *ₛ b *ₛ suc c)
    qed
  
  *ₛ-0 : 0 IsRightUnitOf (_*ₛ_ {1})
  right-unit ⦃ *ₛ-0 ⦄ Finℕ.zero = refl 0

  *ₛ-1 : ∀ {n : ℕ} → (suc (zero {n})) IsRightUnitOf (_*ₛ_ {suc (suc n)})
  right-unit ⦃ *ₛ-1 {n} ⦄ a = 
    proof a *ₛ (suc (zero {n}))
      〉 _==_ 〉 cap (suc n) (toℕ a * 1) :by: refl (a *ₛ (suc (zero {n})))
      〉 _==_ 〉 cap (suc n) (toℕ a) :by: ap (cap (suc n)) $ right-unit {_∙_ = _*_} (toℕ a)
      〉 _==_ 〉 a                   :by: cap-toℕ
    qed

  0-*ₛ : 0 IsLeftUnitOf (_*ₛ_ {1})
  0-*ₛ = left-unit-of-commutative-right-unit 0 _*ₛ_

  1-*ₛ : ∀ {n} → 1 IsLeftUnitOf (_*ₛ_ {suc (suc n)})
  1-*ₛ {n} = left-unit-of-commutative-right-unit 1 _*ₛ_

private
  *unit : (n : ℕ) → Finℕ (suc n)
  *unit 0 = 0
  *unit (suc _) = 1
    
instance
  MonoidFinℕ* : ∀ {n} → FormMonoid (_*ₛ_ {suc n}) (*unit n)

FormMonoid.unit (MonoidFinℕ* {0}) = DefaultUnit
FormMonoid.unit (MonoidFinℕ* {suc n}) = DefaultUnit

instance
  0-IsLeftZeroOf-*ₛ : 0 IsLeftZeroOf (_*ₛ_ {n +1})
  0-IsRightZeroOf-*ₛ : 0 IsRightZeroOf (_*ₛ_ {n +1})

left-zero ⦃ 0-IsLeftZeroOf-*ₛ ⦄ _ = cap-n-zero==zero
right-zero ⦃ 0-IsRightZeroOf-*ₛ ⦄ a =
  proof a *ₛ 0
    === 0 *ₛ a :by: comm a 0
    === 0      :by: left-zero a
  qed

instance
  FormHemiringFinℕ+* : ∀ {n} → FormHemiring (_+ₛ_ {suc n}) _*ₛ_ 0

*[+]==*+* ⦃ FormHemiringFinℕ+* {n} ⦄ zero b c = ap (cap n) $ sym $
  (proof toℕ (cap n zero) + toℕ (cap n zero)
    〉 _==_ 〉 toℕ (cap n zero)
      :by: ap (λ – → toℕ – + toℕ (cap n zero)) $ cap-n-zero==zero {n}
    〉 _==_ 〉 zero
      :by: ap toℕ $ cap-n-zero==zero {n}
  qed)
*[+]==*+* ⦃ FormHemiringFinℕ+* {n} ⦄ (suc a) b c =
  proof suc a *ₛ (b +ₛ c)
    〉 _==_ 〉 cap n (suc (toℕ a) * toℕ (cap n $' toℕ b + toℕ c))
      :by: refl (suc a *ₛ (b +ₛ c))
    〉 _==_ 〉 cap n (suc (toℕ a) * (toℕ b + toℕ c))
      :by: cap-thm (suc (toℕ a) *_) $
           postfix (suc (toℕ a) *_) ⦃ Postfix-*-left-≤ {toℕ a} ⦄
    〉 _==_ 〉 cap n (suc (toℕ a) * toℕ b + suc (toℕ a) * toℕ c)
      :by: ap (cap n) $ *[+]==*+* (suc $' toℕ a) (toℕ b) (toℕ c)
    〉 _==_ 〉 cap n (toℕ (cap n $' suc (toℕ a) * toℕ b) + suc (toℕ a) * toℕ c)
      :by: sym $
             cap-thm (_+ suc (toℕ a) * toℕ c) $
             postfix (_+ suc (toℕ a) * toℕ c)
    〉 _==_ 〉 cap n (toℕ (suc a *ₛ b) + toℕ (cap n $' suc (toℕ a) * toℕ c))
      :by: sym $
             cap-thm (toℕ (suc a *ₛ b) +_) $
             postfix (toℕ (suc a *ₛ b) +_)
    〉 _==_ 〉 suc a *ₛ b +ₛ suc a *ₛ c :by: refl (suc a *ₛ b +ₛ suc a *ₛ c)
  qed
[+]*==*+* ⦃ FormHemiringFinℕ+* ⦄ a b c =
  proof
    (a +ₛ b) *ₛ c
      〉 _==_ 〉 c *ₛ (a +ₛ b) :by: comm (a +ₛ b) c
      〉 _==_ 〉 c *ₛ a +ₛ c *ₛ b :by: *[+]==*+* c a b
      〉 _==_ 〉 c *ₛ a +ₛ b *ₛ c :by: ap (c *ₛ a +ₛ_) $ comm c b
      〉 _==_ 〉 a *ₛ c +ₛ b *ₛ c :by: ap (_+ₛ b *ₛ c) $ comm c a
  qed

HemiringFinℕ+* : Hemiring (Finℕ (suc n))
Hemiring._+_ HemiringFinℕ+* = _+ₛ_
Hemiring._*_ HemiringFinℕ+* = _*ₛ_
Hemiring.zero HemiringFinℕ+* = 0

