{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Permutation where

open import Data.Vec.Definition

open import PropUniverses
open import Data.Nat
open import Relation.Binary hiding (_~_; Symmetric~; step)

-- private
--   variable
--     x y : X
--     v v₀ v₁ v₂ : Vec X m

-- data _~_ {X : 𝒰 ˙} : BinRel 𝒰 (Vec X m) where
--   refl : (v : Vec X m) → v ~ v
--   trans : (p : v₀ ~ v₁) (q : v₁ ~ v₂) → v₀ ~ v₂
--   swap : (x y : X) (p : v₀ ~ v₁) → x ∷ y ∷ v₀ ~ y ∷ x ∷ v₁
--   step : (x : X) (p : v₀ ~ v₁) → x ∷ v₀ ~ x ∷ v₁

-- instance
--   ReflexivePerm : Reflexive (_~_ {X = X}{m})
--   TransitivePerm : Transitive (_~_ {X = X}{m})
--   SymmetricPerm : Symmetric (_~_ {X = X}{m})

-- refl' ⦃ ReflexivePerm ⦄ = refl

-- trans' ⦃ TransitivePerm ⦄ = trans

-- sym ⦃ SymmetricPerm ⦄ (refl v) = refl v
-- sym ⦃ SymmetricPerm ⦄ (trans p₁ p₂) = trans (sym p₂) (sym p₁)
-- sym ⦃ SymmetricPerm ⦄ (swap x y p) = swap y x (sym p)
-- sym ⦃ SymmetricPerm ⦄ (step x p) = step x (sym p)

open import Data.Vec.Property
open import Collection
open import Logic
open import Proof

  --       go (_~_.refl l) q = q
  --       go (_~_.trans p q) q' = go q $ go p q'
  --       go (swap {v₀ = v₀}{v₁} x y p) (x∈x∷ (y ∷ t)) = x∈tail y $ x∈x∷ v₁ 
  --       go (swap {v₀ = v₀}{v₁} x y p) (x∈tail x (x∈x∷ t)) = x∈x∷ (x ∷ v₁)
  --       go (swap x y p) (x∈tail x (x∈tail y q)) =
  --         x∈tail y $ x∈tail x $ go p q
  --       go (step {v₀ = v₀}{v₁} x p) (x∈x∷ t) = x∈x∷ v₁
  --       go (step x p) (x∈tail x' q) = x∈tail x' $ go p q

open import Proposition.Decidable
open import Data.Vec.Function

-- module Composable~ {m : ℕ}{X : 𝒰 ˙} where
--   open TransMakeComposable (_~_ {Col = Vec X m}) public

remove-simp : ∀ x (v : Vec X m) p
  ⦃ dec== : HasDecidableIdentity X ⦄
  → -------------------------
  vec-remove x (x ∷ v) p == v
remove-simp x v p ⦃ dec== ⦄ with decide (x == x) ⦃ dec== ⦄
remove-simp x v p ⦃ dec== ⦄ | true p = Id-refl v
remove-simp x v p ⦃ dec== ⦄ | false ¬p =
  ⊥-recursion _ $ ¬p $ Id-refl x

import Proposition.Permutation as Perm
import Data.List as L
open import Proof
open import Logic.Proof
open import Collection.Listable.Proof

to-list~-→-∃-vec : ∀ (v : Vec X m) {l}
  (p : to-list v Perm.~ l)
  → -----------------------------------------
  ∃ λ v' → v' ~ v ∧ to-list v' == l
to-list~-→-∃-vec {X = X} v {l} p with go v p
  where to-list-len~ : ∀ (v : Vec X m){l}
          (p : to-list v ~ l)
          → --------------------------------
          len l == m
        go : ∀ (v : Vec X m) {l}
          (p : to-list v ~ l)
          → ----------------------------------------------------
          ∃ λ n →
          ∃ λ (v' : Vec X n) →
          n == m ∧
          to-list v' ~ to-list v ∧
          to-list v' == l
        go {m = m} v {l} p =
          len l , (
          to-vec l , (
            to-list-len~ v p ,
            (proof to-list (to-vec l)
               〉 _==_ 〉 l             :by: subrel $ to-list-to-vec l
               〉 _~_ 〉 to-list v      :by: sym ⦃ Symmetric~ ⦄ p
             qed) ,
            subrel $ to-list-to-vec l))
        instance _ =  Monoid+
        to-list-len~ {m = m} v {l} p =
          proof len l
            === len (to-list v) :by: sym $ ap (fold-map (λ _ → 1)) p
            === m :by: vec-to-list-len v
          qed
to-list~-→-∃-vec v p | m , (v' , (Id-refl m , v'~v , to-list-v'==l)) =
  v' , (v'~v , to-list-v'==l)

remove-~-preserv : ∀ {X : 𝒰 ˙} x (v v' : Vec X (m +1)) p
  ⦃ dec== : HasDecidableIdentity X ⦄
  (q : v ~ v')
  → ---------------------------------
  vec-remove x v p ~ vec-remove x v' (⟶ (∈-~ x q) p)
remove-~-preserv x [ h ] [ h ] p (rfl _) = rfl _
remove-~-preserv x [ h ] [ h₁ ] p (step (Perm.step h ()) q)
remove-~-preserv x (h₀ ∷ h₁ ∷ v) (h₀' ∷ h₁' ∷ v') p ⦃ dec== ⦄ q
  with decide (h₀ == x) ⦃ dec== ⦄
remove-~-preserv x (h₀ ∷ h₁ ∷ v) (h₀' ∷ h₁' ∷ v') p ⦃ dec== ⦄ q
  | true p₁ = {!!}
remove-~-preserv x (h₀ ∷ h₁ ∷ v) (h₀' ∷ h₁' ∷ v') p ⦃ dec== ⦄ q | false ¬p = {!!}
-- remove-~-preserv x {[ x ]} {[ h ]} (x∈x∷ []) (Perm.trans q₀ q₁)
--   | true p =
--   proof to-list (vec-remove x [ x ] _)
--     〉 _==_ 〉 L.[] :by: ap to-list $ remove-simp x [] _
--     〉 _~_ 〉 L.[]  :by: Perm.empty
--   qed
-- remove-~-preserv x {[ x ]} {[ h ]} (x∈x∷ []) (Perm.trans {l₂ = l₂} q₀ q₁)
--   | false ¬p with ⟶ (
--     proof x ∈ L.[ x ]
--       〉 _↔_ 〉 x ∈ l₂
--         :by: ∈-~ x q₀
--       〉 _↔_ 〉 x ∈ L.[ h ]
--         :by: ∈-~ x q₁
--     qed) $ L.x∈x∷ L.[]
-- remove-~-preserv x {[ x ]} {[ x ]} (x∈x∷ []) (Perm.trans q₀ q₁)
--   | false ¬p | L.x∈x∷ L.[] = ⊥-recursion _ $ ¬p $ Id-refl x
-- remove-~-preserv {m = zero} x [ x ] [ x ] (x∈x∷ []) (Perm.step x q) =
--   refl (vec-remove x [ x ] _) 
-- remove-~-preserv x (h₀ ∷ h₁ ∷ v) (h₀' ∷ h₁' ∷ v') p (Perm.trans q₀ q₁)
--   with to-list~-→-∃-vec (h₀ ∷ h₁ ∷ v) q₀
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₀' ∷ h₁' ∷ v'} p (Perm.trans q₀ q₁)
--   | v₂ , (q₂ , Id-refl .(to-list v₂)) =
--   -- TODO: figure out why composing vector _~_ throws errors
--   proof to-list (vec-remove x (h₀ ∷ h₁ ∷ v) p)
--     〉 _~_ 〉 to-list (vec-remove x v₂ _)
--       :by: remove-~-preserv x (h₀ ∷ h₁ ∷ v) v₂ p q₀
--     〉 _~_ 〉 to-list (vec-remove x (h₀' ∷ h₁' ∷ v') _)
--       :by: remove-~-preserv x v₂ (h₀' ∷ h₁' ∷ v') (⟵ (∈-~ x q₂) p) q₁
--   qed
-- remove-~-preserv x (h₀ ∷ h₁ ∷ v)(h₁ ∷ h₀ ∷ v') p ⦃ dec== ⦄ (Perm.swap h₀ h₁ q)
--   with decide (h₀ == x) ⦃ dec== ⦄
-- remove-~-preserv x {x ∷ h₁ ∷ v} {h₁ ∷ x ∷ v'} p ⦃ dec== ⦄ (Perm.swap x h₁ q)
--   | true (Id-refl x) with decide (h₁ == x) ⦃ dec== ⦄
-- remove-~-preserv x {x ∷ x ∷ v} {x ∷ x ∷ v'} p (Perm.swap x x q)
--   | true (Id-refl x) | true (Id-refl x) = Perm.step x q
-- remove-~-preserv x {x ∷ h₁ ∷ v} {h₁ ∷ x ∷ v'} p ⦃ dec== ⦄ (Perm.swap x h₁ q)
--   | true (Id-refl x) | false ¬p with decide (x == x) ⦃ dec== ⦄
-- remove-~-preserv x {x ∷ h₁ ∷ v} {h₁ ∷ x ∷ v'} p (Perm.swap x h₁ q)
--   | true (Id-refl x) | false ¬p | true _ = Perm.step h₁ q
-- remove-~-preserv x {x ∷ h₁ ∷ v} {h₁ ∷ x ∷ v'} p (Perm.swap x h₁ q)
--   | true (Id-refl x) | false ¬p | false ¬p₁ =
--   ⊥-recursion _ $ ¬p₁ $ Id-refl x
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₁ ∷ h₀ ∷ v'} p ⦃ dec== ⦄ (Perm.swap h₀ h₁ q)
--   | false ¬p with decide (h₁ == x) ⦃ dec== ⦄
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₁ ∷ h₀ ∷ v'} p (Perm.swap h₀ h₁ q)
--   | false ¬p | true p₁ = Perm.step h₀ q
-- remove-~-preserv x {x ∷ h₁ ∷ v} {h₁ ∷ x ∷ v'} (x∈x∷ h₁ ∷ v) (Perm.swap x h₁ q)
--   | false ¬p | false ¬p₁ =
--   ⊥-recursion _ $ ¬p $ Id-refl x
-- remove-~-preserv x {h₀ ∷ x ∷ v} {x ∷ h₀ ∷ v'} (x∈tail h₀ (x∈x∷ v)) (Perm.swap h₀ x q)
--   | false ¬p | false ¬p₁ =
--   ⊥-recursion _ $ ¬p₁ $ Id-refl x
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₁ ∷ h₀ ∷ v'}
--   (x∈tail h₀ (x∈tail h₁ p)) ⦃ dec== ⦄ (Perm.swap h₀ h₁ q)
--   | false ¬p | false ¬p₁ with decide (h₀ == x) ⦃ dec== ⦄
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₁ ∷ h₀ ∷ v'}
--   (x∈tail h₀ (x∈tail h₁ p)) (Perm.swap h₀ h₁ q)
--   | false ¬p₁ | false ¬p₂ | true p₁ =
--   ⊥-recursion _ $ ¬p₁ p₁
-- remove-~-preserv x {h₀ ∷ h₁ ∷ h ∷ v} {h₁ ∷ h₀ ∷ h' ∷ v'}
--   (x∈tail h₀ (x∈tail h₁ p)) ⦃ _ ⦄ (Perm.swap h₀ h₁ q)
--   | false ¬p | false ¬p₁ | false ¬p₂ =
--   Perm.swap h₀ h₁ $ remove-~-preserv x (h ∷ v) (h' ∷ v') p q
-- remove-~-preserv x (h₀ ∷ h₁ ∷ v)(h₀ ∷ h₁' ∷ v') p ⦃ dec== ⦄ (Perm.step h₀ q)
--   with decide (h₀ == x) ⦃ dec== ⦄
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₀ ∷ h₁' ∷ v'} p (Perm.step h₀ q) | true _ = q
-- remove-~-preserv x {x ∷ h₁ ∷ v} {x ∷ h₁' ∷ v'} (x∈x∷ (h₁ ∷ v)) (Perm.step x q)
--   | false ¬p = ⊥-recursion _ $ ¬p $ Id-refl x
-- remove-~-preserv x {h₀ ∷ h₁ ∷ v} {h₀ ∷ h₁' ∷ v'} (x∈tail h₀ p) (Perm.step h₀ q)
--   | false _ = Perm.step h₀ $ remove-~-preserv x (h₁ ∷ v)(h₁' ∷ v') p q

-- remove-~-preserv x p (refl v) = refl (vec-remove x v p)
-- remove-~-preserv x p (trans {v₀ = v₀}{v₁}{v₂} q q') =
--   proof vec-remove x v₀ p
--     〉 _~_ 〉 vec-remove x v₁ _
--       :by: remove-~-preserv x p q
--     〉 _~_ 〉 vec-remove x v₂ _
--       :by: remove-~-preserv x (⟶ (∈-~ x q) p) q'
--   qed
-- remove-~-preserv x p ⦃ dec== ⦄ (swap x' y' q)
--   with decide (x' == x) ⦃ dec== ⦄
-- remove-~-preserv x p ⦃ dec== ⦄ (swap x y' q)
--   | true (Id-refl x) with decide (y' == x) ⦃ dec== ⦄
-- remove-~-preserv x p ⦃ dec== ⦄ (swap x x q)
--   | true (Id-refl x) | true (Id-refl x) = step x q
-- remove-~-preserv x p ⦃ dec== ⦄ (swap {v₀ = v₀}{v₁} x y' q)
--   | true (Id-refl x) | false ¬p = step y' (
--     proof v₀
--       〉 _~_ 〉 v₁ :by: q
--       〉 _==_ 〉 vec-remove x (x ∷ v₁) _
--         :by: sym $ remove-simp x v₁ _
--     qed)
-- remove-~-preserv x p ⦃ dec== ⦄ (swap {v₀ = v₀}{v₁} x' y' q)
--   | false ¬p with decide (y' == x) ⦃ dec== ⦄
-- remove-~-preserv x p ⦃ dec== ⦄ (swap {v₀ = v₀}{v₁} x' x q)
--   | false ¬p | true (Id-refl x) = step x' q
-- remove-~-preserv x (x∈x∷ (y' ∷ _)) ⦃ dec== ⦄ (swap x y' q)
--   | false ¬p | false ¬p₁ = ⊥-recursion _ $ ¬p $ Id-refl x
-- remove-~-preserv x (x∈tail x' (x∈x∷ t)) ⦃ dec== ⦄ (swap x' x q)
--   | false ¬p | false ¬p₁ = ⊥-recursion _ $ ¬p₁ $ Id-refl x
-- remove-~-preserv x (x∈tail x' (x∈tail y' p)) ⦃ dec== ⦄ (swap x' y' q)
--   | false ¬p | false ¬p₁ with decide (x' == x) ⦃ dec== ⦄
-- remove-~-preserv x (x∈tail x' (x∈tail y' p)) ⦃ dec== ⦄ (swap x' y' q)
--   | false ¬p₀ | false ¬p₁ | true p₀ = ⊥-recursion _ $ ¬p₀ p₀
-- remove-~-preserv x (x∈tail x' (x∈tail y' p)) ⦃ dec== ⦄
--   (swap {v₀ = h ∷ v₀} x' y' q) | false ¬p | false ¬p₁ | false ¬p₂ =
--   swap x' y' $ remove-~-preserv x p q
-- remove-~-preserv x p ⦃ dec== ⦄ (step x' q) with decide (x' == x) ⦃ dec== ⦄
-- remove-~-preserv x p ⦃ dec== ⦄ (step x' q) | true _ = q
-- remove-~-preserv x (x∈x∷ t) ⦃ dec== ⦄ (step x q) | false ¬p =
--   ⊥-recursion _ $ ¬p $ Id-refl x
-- remove-~-preserv {m = m +1} x (x∈tail x' p) ⦃ dec== ⦄ (step x' q) | false ¬p =
--   step x' (remove-~-preserv x p q)

open import Proposition.Identity hiding (refl)

vec-remove-~ : ∀ h (t : Vec X m) v p
  ⦃ dec== : HasDecidableIdentity X ⦄
  → ------------------------------
  h ∷ t ~ v ↔ t ~ vec-remove h v p
vec-remove-~ = {!!}
-- ⟶ (vec-remove-~ h [] [ h ] (x∈x∷ [])) q =
--   proof L.[]
--     〉 _~_ 〉 L.[]   :by: refl []
--     〉 _==_ 〉 to-list (vec-remove h [ h ] _)
--       :by: ap to-list $ sym $ remove-simp h [] _
--   qed
-- ⟶ (vec-remove-~ h (h₂ ∷ t) (h₁ ∷ h₃ ∷ v) p) (Perm.trans q₀ q₁)
--   with to-list~-→-∃-vec (h ∷ h₂ ∷ t) q₀
-- ⟶ (vec-remove-~ h (h₂ ∷ t) (h₁ ∷ h₃ ∷ v) p ⦃ dec== ⦄) (Perm.trans q₀ q₁)
--   | v' , (v'~h∷h₂∷t , Id-refl .(to-list v')) =
--   proof to-list (h₂ ∷ t)
--     〉 _~_ 〉 to-list (vec-remove h v'
--               (⟵ (∈-~ h v'~h∷h₂∷t) (x∈x∷ h₂ ∷ t)))
--       :by: ⟶ (vec-remove-~ h (h₂ ∷ t) v' _) q₀
--     〉 _~_ 〉 to-list (vec-remove h (h₁ ∷ h₃ ∷ v) p)
--       :by: remove-~-preserv h v' (h₁ ∷ h₃ ∷ v) _ q₁
--   qed
-- ⟶ (vec-remove-~ h (h₂ ∷ t) (fh₂ ∷ h ∷ v) p ⦃ dec== ⦄) 
--   (Perm.swap h h₂ q) with decide (h₂ == h) ⦃ dec== ⦄
-- ⟶ (vec-remove-~ h (h ∷ t) (h ∷ h ∷ v) p) (Perm.swap h h q)
--   | true (Id-refl h) = Perm.step h q 
-- ⟶ (vec-remove-~ h (h₂ ∷ t) (h₂ ∷ h ∷ v) p) (Perm.swap h h₂ q)
--   | false ¬p = Perm.step h₂ (
--     proof to-list t
--       〉 _~_ 〉 to-list v     :by: q
--       〉 _==_ 〉 to-list (vec-remove h (h ∷ v) _)
--         :by: ap to-list $ sym $ remove-simp h v _
--     qed)
-- ⟶ (vec-remove-~ h (h₂ ∷ t) (h ∷ h₃ ∷ v) p) (Perm.step h q) =
--   proof to-list (h₂ ∷ t)
--     〉 _~_ 〉 to-list (h₃ ∷ v)   :by: q 
--     〉 _==_ 〉 to-list (vec-remove h (h ∷ h₃ ∷ v) p)
--       :by: ap to-list $ sym $ remove-simp h (h₃ ∷ v) p
--   qed
-- ⟵ (vec-remove-~ h t (h₁ ∷ v) p ⦃ dec== ⦄) q
--   with decide (h₁ == h) ⦃ dec== ⦄
-- ⟵ (vec-remove-~ h t (h ∷ v) p) q | true (Id-refl h) = Perm.step h q
-- ⟵ (vec-remove-~ h [] [ h ] (x∈x∷ [])) q | false ¬p = refl [ h ]
-- ⟵ (vec-remove-~ h (h₃ ∷ t) (h₁ ∷ h₂ ∷ v) p ⦃ dec== ⦄) q | false ¬p
--   with decide (h₂ == h) ⦃ dec== ⦄
-- ⟵ (vec-remove-~ h (h₃ ∷ t) (h₁ ∷ h ∷ v) p) q
--   | false ¬p | true (Id-refl h) =
--   proof to-list (h ∷ h₃ ∷ t)
--     〉 _~_ 〉 to-list (h ∷ h₁ ∷ v)
--       :by: Perm.step h q
--     〉 _~_ 〉 to-list (h₁ ∷ h ∷ v)
--       :by: Perm.swap h h₁ $ refl v
--   qed
-- ⟵ (vec-remove-~ h [ h₃ ] [ h ⸴ h₂ ] (x∈x∷ [ h₂ ])) q
--   | false ¬p | false ¬p₁ = ⊥-recursion _ $ ¬p $ Id-refl h
-- ⟵ (vec-remove-~ h [ h₃ ] [ h₁ ⸴ h ] (x∈tail h₁ (x∈x∷ []))) q
--   | false ¬p | false ¬p₁ = ⊥-recursion _ $ ¬p₁ $ Id-refl h
-- ⟵ (vec-remove-~ h (h₃ ∷ h₅ ∷ t) (h₁ ∷ h₂ ∷ h₄ ∷ v) p) (Perm.trans q₀ q₁) | false ¬p | false ¬p₁ = {!!}
-- ⟵ (vec-remove-~ h (h₂ ∷ h₁ ∷ t) (h₁ ∷ h₂ ∷ h₄ ∷ v) p) (Perm.swap h₂ h₁ q) | false ¬p | false ¬p₁ = {!!}
-- ⟵ (vec-remove-~ h (.h₁ ∷ h₅ ∷ t) (h₁ ∷ h₂ ∷ h₄ ∷ v) p ⦃ _ ⦄) (Perm.step .h₁ q) | false ¬p | false ¬p₁ = {!!}

-- ⟶ (vec-remove-~ h t v p) (trans {v₀}{v₁}{v₂} p₁ p₂) =
--   proof t
--     〉 _~_ 〉 vec-remove h v₂ _
--       :by: ⟶ (vec-remove-~ h t v₂ $ ⟶ (∈-~ h p₁) (x∈x∷ t)) p₁
--     〉 _~_ 〉 vec-remove h v p
--       :by: remove-~-preserv h _ p₂ 
--   qed
-- ⟶ (vec-remove-~ h t (h ∷ t) p ⦃ dec== ⦄) (refl (h ∷ t))
--   with decide (h == h) ⦃ dec== ⦄
-- ⟶ (vec-remove-~ h t (h ∷ t) p ⦃ dec== ⦄) (refl .(h ∷ t)) | true _ =
--   refl t
-- ⟶ (vec-remove-~ h t (h ∷ t) p ⦃ dec== ⦄) (refl .(h ∷ t)) | false ¬h==h =
--   ⊥-recursion _ $ ¬h==h $ refl' h
-- ⟶ (vec-remove-~ h (y ∷ _) (y ∷ h ∷ _) p ⦃ dec== ⦄) (swap h y q)
--   with decide (y == h) ⦃ dec== ⦄
-- ⟶ (vec-remove-~ h (h ∷ _) (h ∷ h ∷ _) p ⦃ dec== ⦄) (swap h h q)
--   | true (Id-refl h) = step h q
-- ⟶ (vec-remove-~ h (y ∷ _) (y ∷ h ∷ _) p ⦃ dec== ⦄) (swap {v₀ = v₀}{v₁} h y q)
--   | false ¬p = step y (
--    proof v₀
--     〉 _~_ 〉 v₁ :by: q
--     〉 _==_ 〉 vec-remove h (h ∷ v₁) _
--       :by: sym $ remove-simp h v₁ _
--   qed)
-- ⟶ (vec-remove-~ h t (h ∷ _) p) (step {v₀ = v₀}{v₁} h q) =
--   proof v₀
--     〉 _~_ 〉 v₁ :by: q
--     〉 _==_ 〉 vec-remove h (h ∷ v₁) p
--       :by: sym $ remove-simp h v₁ _
--   qed
-- ⟵ (vec-remove-~ h t (h ∷ v) (x∈x∷ v)) q = step h (
--   proof t
--     〉 _~_ 〉 vec-remove h (h ∷ v) _ :by: q
--     〉 _==_ 〉 v                     :by: remove-simp h v _
--   qed)
-- ⟵ (vec-remove-~ h t (h₁ ∷ v) (x∈tail h₁ p) ⦃ dec== ⦄) q
--   with decide (h₁ == h) ⦃ dec== ⦄
-- ⟵ (vec-remove-~ h t (h ∷ v) (x∈tail h p)) q
--   | true (Id-refl h) = step h q
-- ⟵ (vec-remove-~ {m = 1} h [ t₀ ] [ v₀ ⸴ h ] (x∈tail v₀ (x∈x∷ []))) q
--   | false ¬p =
--   proof [ h ⸴ t₀ ]
--     〉 _~_ 〉 [ h ⸴ v₀ ]
--       :by: step h $
--            Id.coe (ap (λ — → [ t₀ ] ~ v₀ ∷ —) $ remove-simp h [] _) q
--     〉 _~_ 〉 [ v₀ ⸴ h ]
--       :by: swap h v₀ (refl [])
--   qed
-- ⟵ (vec-remove-~ {m = m +2} h (h₂ ∷ t) (h₁ ∷ v) (x∈tail h₁ p)) q
--   | false ¬p =
--   proof h ∷ h₂ ∷ t
--     〉 _~_ 〉 h ∷ h₁ ∷ vec-remove h v p
--       :by: step h q
--     〉 _~_ 〉 h₁ ∷ h ∷ vec-remove h v p
--       :by: swap h h₁ $ refl (vec-remove h v p) 
--     〉 _~_ 〉 h₁ ∷ v
--       :by: step h₁ $
--            ⟵ (vec-remove-~ h (vec-remove h v p) v p) $
--            refl (vec-remove h v p)
--   qed

import Data.NonemptyList as NL

preserv-~-vec-to-nonempty-list :
  {v v' : Vec X (m +1)}
  → -------------------------------------------------------------
  v ~ v' ↔ vec-to-nonempty-list v ~ vec-to-nonempty-list v'
preserv-~-vec-to-nonempty-list = {!!}
-- ⟶ preserv-~-vec-to-nonempty-list (refl v) =
--   NLP.refl (vec-to-nonempty-list v)
-- ⟶ preserv-~-vec-to-nonempty-list (trans p₀ p₁) =
--   NLP.trans (⟶ preserv-~-vec-to-nonempty-list p₀)
--             (⟶ preserv-~-vec-to-nonempty-list p₁)
-- ⟶ preserv-~-vec-to-nonempty-list (swap {v₀ = []}{[]} x y p) =
--   NLP.swap-base x y
-- ⟶ preserv-~-vec-to-nonempty-list (swap {v₀ = h₀ ∷ v₀}{h₁ ∷ v₁} x y p) =
--   NLP.swap-step x y $ ⟶ preserv-~-vec-to-nonempty-list p
-- ⟶ preserv-~-vec-to-nonempty-list (step {v₀ = []}{[]} x p) = NLP.refl NL.[ x ]
-- ⟶ preserv-~-vec-to-nonempty-list (step {v₀ = h₀ ∷ v₀}{h₁ ∷ v₁} x p) =
--   NLP.step x $ ⟶ preserv-~-vec-to-nonempty-list p
-- ⟵ (preserv-~-vec-to-nonempty-list {v = [ h ]} {[ h ]}) (NLP.refl NL.[ h ]) =
--   refl [ h ]
-- ⟵ (preserv-~-vec-to-nonempty-list {v = [ h ]} {[ h' ]}) (NLP.trans {l₂ = NL.[ x ]} q₀ q₁) = {!!}
-- ⟵ (preserv-~-vec-to-nonempty-list {v = [ h ]} {[ h' ]}) (NLP.trans {l₂ = h₁ NL.∷ l₂} q₀ q₁) = {!!}
-- ⟵ (preserv-~-vec-to-nonempty-list {v = h₀ ∷ h₁ ∷ v} {h₀' ∷ h₁' ∷ v'}) q = {!!}
