{-# OPTIONS --exact-split --safe --prop #-}
module Data.Nat.Property where

open import Data.Nat.Definition
open import Data.Nat.Arithmetic
open import Data.Nat.Order
open import Data.Nat.Syntax
open Pattern

open import Proposition.Identity hiding (refl)
open import Proposition.Decidable
open import Function.Property

open import Operation.Binary.Property
open import Relation.Binary.Property
open import Logic
open import Proof
open import Function.Proof
open import Data.Nat.Proof

instance
  Injective-suc : Injective suc
  Surjective-pred : Surjective pred
  Decidableℕ== : Decidable (n == m)
  Relating-+-left-< : Relating (m +_) _<_ _<_
  Relating-+-right-< : Relating (_+ m) _<_ _<_
  Relating-+-left-≤ : Relating (m +_) _≤_ _≤_
  Relating-+-right-≤ : Relating (_+ m) _≤_ _≤_
  Relating-2-+-<-< : Relating-2 _+_ _<_ _<_ _<_
  Relating-2-+-≤-≤ : Relating-2 _+_ _≤_ _≤_ _≤_
  Relating-2-+-<-≤ : Relating-2 _+_ _<_ _≤_ _<_
  Relating-2-+-≤-< : Relating-2 _+_ _≤_ _<_ _<_
  Postfix-+-left-< : UniversalPostfix (suc n +_) _<_
  Postfix-+-right-< : UniversalPostfix (_+ suc n) _<_
  Postfix-+-left-≤ : UniversalPostfix (n +_) _≤_
  Postfix-+-right-≤ : UniversalPostfix (_+ n) _≤_
  Postfix-*-left-≤ : UniversalPostfix (suc n *_) _≤_
  Postfix-*-right-≤ : UniversalPostfix (_* suc n) _≤_

inj ⦃ Injective-suc ⦄ (Id.refl (suc m)) = refl m

surj ⦃ Surjective-pred ⦄ y = suc y , refl y

Decidableℕ== {zero} {zero} = true (refl zero)
Decidableℕ== {zero} {suc n} = false λ ()
Decidableℕ== {suc m} {zero} = false λ ()
Decidableℕ== {suc m} {suc n} with decide (m == n)
Decidableℕ== {suc m} {suc n} | true n==m = true (ap suc n==m)
Decidableℕ== {suc m} {suc n} | false ¬n==m =
  false λ { (Id.refl (suc m)) → ¬n==m (refl m) }

rel-preserv ⦃ Relating-+-left-< {zero} ⦄ a<b = a<b
rel-preserv ⦃ Relating-+-left-< {m +1} ⦄ a<b =
  ap suc ⦃ Relating-suc-< ⦄ $ rel-preserv a<b
rel-preserv ⦃ Relating-+-right-< {m} ⦄ {a}{b} a<b =
  proof a + m
    〉 _==_ 〉 m + a :by: comm a m
    〉 _<_ 〉  m + b :by: ap (m +_) a<b
    〉 _==_ 〉 b + m :by: comm m b
  qed
rel-preserv ⦃ Relating-+-left-≤ {m} ⦄ (∨left (Id.refl a)) = refl (m + a)
rel-preserv ⦃ Relating-+-left-≤ {m} ⦄ (∨right q) = ∨right $ ap (m +_) q
rel-preserv ⦃ Relating-+-right-≤ {m} ⦄ {a}{b} a≤b =
  proof a + m
    〉 _==_ 〉 m + a :by: comm a m
    〉 _≤_ 〉  m + b :by: ap (m +_) a≤b
    〉 _==_ 〉 b + m :by: comm m b
  qed

rel-preserv-2 ⦃ Relating-2-+-<-< ⦄ {x}{x'}{y}{y'} x<x' y<y' =
  proof x + y
    〉 _<_ 〉 x' + y  :by: ap (_+ y) x<x'
    〉 _<_ 〉 x' + y' :by: ap (x' +_) y<y'
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
    〉 _≤_ 〉 x' + y  :by: ap (_+ y) x≤x'
    〉 _<_ 〉 x' + y' :by: ap (x' +_) y<y'
  qed

UniversalPostfix.postfix (Postfix-+-left-< {zero}) =
  postfix suc ⦃ Postfix-suc-< ⦄
UniversalPostfix.postfix (Postfix-+-left-< {suc n}) x =
  proof x
    〉 _<_ 〉 suc n + x   :by: postfix (suc n +_) x
    〉 _<_ 〉 suc (suc n + x)
      :by: postfix suc ⦃ Postfix-suc-< ⦄ (suc n + x)
  qed

UniversalPostfix.postfix (Postfix-+-right-< {n}) x =
  proof x
    〉 _<_ 〉 suc n + x :by: postfix (suc n +_) x
    〉 _==_ 〉 x + suc n :by: comm (suc n) x
  qed

UniversalPostfix.postfix (Postfix-+-left-≤ {zero}) x = refl x
UniversalPostfix.postfix (Postfix-+-left-≤ {suc n}) x =
  ∨right (postfix (suc n +_) x)

UniversalPostfix.postfix (Postfix-+-right-≤ {n}) x =
  proof x
    〉 _≤_ 〉 n + x :by: postfix (n +_) x
    〉 _==_ 〉 x + n :by: comm n x
  qed

UniversalPostfix.postfix (Postfix-*-left-≤ {n}) x =
  postfix (_+ n * x) ⦃ Postfix-+-right-≤ ⦄ x

UniversalPostfix.postfix (Postfix-*-right-≤ {n}) x =
  proof x
    〉 _≤_ 〉 suc n * x :by: postfix (suc n *_) ⦃ Postfix-*-left-≤ {n} ⦄ x
    〉 _==_ 〉 x * suc n :by: comm (suc n) x
  qed

postfix-sub-< : ∀ {m n} k {p p'}
  (q : m < n)
  → --------------------
  m - k [ p ] < n - k [ p' ]
postfix-sub-< {zero} {_ +1} zero _ = z<s
postfix-sub-< {zero} {_ +1} (_ +1) {Logic.∨left ()}
postfix-sub-< {zero} {_ +1} (_ +1) {∨right ()}
postfix-sub-< {_ +1} {_ +1} zero q = q
postfix-sub-< {m +1} {n +1} (k +1) q = postfix-sub-< k (s<s→-<- q)

-+ : (p : m ≥ k) → m - k [ p ] + k == m
-+ {m}{zero} p = right-unit m
-+ {zero}{k +1} (∨left ())
-+ {zero}{k +1} (∨right ())
-+ {m +1}{k +1} p =
  proof m - k [ ap pred p ] + (k +1)
    === m - k [ ap pred p ] + k +1
      :by: +-suc (m - k [ ap pred p ]) k
    === m +1
      :by: ap suc $ -+ {m}{k} $ ap pred p
  qed

+==→-== :
  (q : m == k + n)
  → ---------------
  m - n [ Id.coe (ap (n ≤_) $ sym q) $ postfix (k +_) n ] == k
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
⟶ (-==0 {p = ∨left p}) q = sym p
⟶ (-==0 {p = ∨right (s<s p)}) q = ap suc $ ⟶ (-==0 {p = ∨right p}) q
⟵ -==0 = +==→-==

open import Relation.Binary

comm-+ : ∀ {a b c}
  (p : b ≤ a)
  → -----------------------
  a - b [ p ] + c == a + c - b [ trans p $ postfix (_+ c) a ]
comm-+ {a}{b}{c} p = sym $ +==→-== $ sym (
  proof a - b [ p ] + c + b
    === a - b [ p ] + b + c
      :by: swap' (a - b [ p ]) c b
    === a + c
      :by: ap (_+ c) $ -+ p
  qed)

relating-≤ : ∀ {a b c}
  (p : b ≤ c)
  (q : c ≤ a)
  → -----------------------
  c - b [ p ] ≤ a - b [ trans p q ]
relating-≤ {a}{b} p (∨left (Id.refl a)) =
  refl (a - b [ p ])
relating-≤ {a +1} {zero} {c +1} p (∨right (s<s q)) =
  ∨right (ap suc q)
relating-≤ {a +1} {b +1} {c +1} p (∨right (s<s q)) =
  relating-≤ (ap pred p) (∨right q)
relating-≤ (∨left (Id.refl 0)) (∨right z<s) =
  ∨right z<s

-comm : ∀ {a b c}
  (p : b ≤ a)
  (q : c + b ≤ a)
  → -----------------------------------------------
  let p₀ = proof c
             〉 _==_ 〉 c + b - b [ postfix (c +_) b ]
               :by: sym $ +==→-== (refl (c + b))
             〉 _≤_ 〉 a - b [ p ]
               :by: relating-≤ (postfix (c +_) b) q
           qed
      p' = trans (postfix (_+ b) c) q
      p₀' = proof b
              〉 _==_ 〉 c + b - c [ _ ]
                :by: sym $ +==→-== $ comm c b
              〉 _≤_ 〉 a - c [ p' ]
                :by: relating-≤  (postfix (_+ b) c) q
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
              :by: relating-≤  (postfix (_+ b) c) q
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
      :by: -== (comm-+ p) (refl c)
    === d + a - a [ _ ] - c [ _ ]
      :by: -== (-== q₁ (refl a)) (refl c)
    === d - c [ q ]
      :by: -== (+==→-== $ refl (d + a)) (refl c)
  qed
