{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Arithmetic.Subtraction.Property where

open import Data.Nat.Arithmetic.Subtraction.Definition

open import Data.Nat.Definition
open import Data.Nat.Syntax
open Pattern
open import Data.Nat.Arithmetic
open import Data.Nat.Order
open import Data.Nat.Property

open import Operation.Binary
open import Logic
open import Proof
open import Function.Proof

relating-sub-≤ : ∀ {m n} k {p p'}
  (q : m ≤ n)
  → --------------------
  m - k [ p ] ≤ n - k [ p' ]
relating-sub-≤ zero q = q
relating-sub-≤ (k +1) (s≤s q) = relating-sub-≤ k q

-+ : (p : k ≤ m) → m - k [ p ] + k == m
-+ {0}{m} p = right-unit m
-+ {k +1}{m +1} p =
  proof m - k [ ap pred p ] + (k +1)
    === m - k [ ap pred p ] + k +1
      :by: +-suc (m - k [ ap pred p ]) k
    === m +1
      :by: ap suc $ -+ {k}{m} $ ap pred p
  qed

+==→-== :
  (q : m == k + n)
  → ---------------
  let p = Id.coe (ap (n ≤_) $ sym q) $ postfix (k +_) n in
  m - n [ p ] == k
+==→-== {.(k + 0)}{k}{zero} (Id.refl .(k + 0)) = right-unit k
+==→-== {.(k + (n +1))}{k} {n +1} (Id.refl .(k + (n +1))) =
  proof k + (n +1) - (n +1) [ p ]
    === k + n +1 - (n +1) [ Id.coe (ap (n +1 ≤_) (+-suc k n)) p  ]
      :by: -== (+-suc k n) (refl (n +1))
    === k + n - n [ postfix (k +_) n  ]
      :by: Id.refl _
    === k
      :by: +==→-== (refl (k + n))
  qed
  where p = postfix (k +_) (n +1)

-==0 : ∀ {a b p}
  → ------------------
  a - b [ p ] == 0 ↔ a == b
⟶ (-==0 {p = z≤ m}) q = q
⟶ (-==0 {p = s≤s p}) q = ap suc $ ⟶ -==0 q
⟵ -==0 = +==→-==

open import Relation.Binary

suc- : ∀{a b} p
  → -------------------
  a - b [ p ] +1 == a +1 - b [ trans p $ postfix suc a ]
suc- (z≤ a) = Id.refl (a +1)
suc- (s≤s p) = suc- p

-+comm : ∀ {a b c}
  (p : b ≤ a)
  → -----------------------
  a - b [ p ] + c == a + c - b [ trans p $ postfix (_+ c) a ]
-+comm {a}{b}{c} p = sym $ +==→-== $ sym (
  proof a - b [ p ] + c + b
    === a - b [ p ] + b + c
      :by: swap' (a - b [ p ]) c b
    === a + c
      :by: ap (_+ c) $ -+ p
  qed)

relating---≤ : ∀ {a b c}
  (p : b ≤ c)
  (q : c ≤ a)
  → -----------------------
  c - b [ p ] ≤ a - b [ trans p q ]
relating---≤ (z≤ m) q = q
relating---≤ (s≤s p) (s≤s q) = relating---≤ p q

-comm : ∀ {a b c}
  (p : b ≤ a)
  (q : c + b ≤ a)
  → -----------------------------------------------
  let p₀ = proof c
             〉 _==_ 〉 c + b - b [ postfix (c +_) b ]
               :by: sym $ +==→-== (refl (c + b))
             〉 _≤_ 〉 a - b [ p ]
               :by: relating---≤ (postfix (c +_) b) q
           qed
      p' = trans (postfix (_+ b) c) q
      p₀' = proof b
              〉 _==_ 〉 c + b - c [ _ ]
                :by: sym $ +==→-== $ comm c b
              〉 _≤_ 〉 a - c [ p' ]
                :by: relating---≤  (postfix (_+ b) c) q
            qed
  in
  a - b [ p ] - c [ p₀ ] == a - c [ p' ] - b [ p₀' ]
-comm {a}{b}{c} p q = +==→-== $ +==→-== $ sym (
  proof a - c [ p' ] - b [ p₀' ] + c + b
    === a - c [ p' ] - b [ p₀' ] + b + c
      :by: swap' _ c b
    === a - c [ p' ] + c
      :by: ap (_+ c) $ -+ p₀'
    === a
      :by: -+ p'
  qed)
  where p' = trans (postfix (_+ b) c) q
        p₀' =
          proof b
            〉 _==_ 〉 c + b - c [ _ ]
              :by: sym $ +==→-== $ comm c b
            〉 _≤_ 〉 a - c [ p' ]
              :by: relating---≤  (postfix (_+ b) c) q
          qed

open import Proposition.Proof

-==-↔+==+ : ∀ {a b c d}
  (p : a ≤ b)
  (q : c ≤ d)
  → ------------------
  b - a [ p ] == d - c [ q ] ↔ b + c == d + a
⟶ (-==-↔+==+ {a}{b}{c}{d} p q) p₁ =
  proof b + c
    === b - a [ p ] + a + c
      :by: ap (_+ c) $ sym $ -+ p
    === b - a [ p ] + (a + c)
      :by: sym $ assoc _ a c
    === d - c [ q ] + (a + c)
      :by: ap (_+ (a + c)) $ p₁
    === d - c [ q ] + (c + a)
      :by: ap (d - c [ q ] +_) $ comm a c
    === d - c [ q ] + c + a
      :by: assoc _ c a
    === d + a
      :by: ap (_+ a) $ -+ q
  qed
⟵ (-==-↔+==+ {a}{b}{c}{d} p q) q₁ =
  proof b - a [ p ]
    === b - a [ p ] + c - c [ _ ]
      :by: sym $ +==→-== $ refl (b - a [ p ] + c)
    === b + c - a [ _ ] - c [ _ ]
      :by: -== (-+comm p) (refl c)
    === d + a - a [ _ ] - c [ _ ]
      :by: -== (-== q₁ (refl a)) (refl c)
    === d - c [ q ]
      :by: -== (+==→-== $ refl (d + a)) (refl c)
  qed
