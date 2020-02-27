{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Permutation where

open import Data.Vec.Definition

open import PropUniverses
open import Data.Nat
open import Relation.Binary
  renaming (refl to refl'; trans to trans')
  hiding (_~_)

private
  variable
    x y : X
    v v₀ v₁ v₂ : Vec X m

data _~_ {X : 𝒰 ˙} : BinRel 𝒰 (Vec X m) where
  refl : (v : Vec X m) → v ~ v
  trans : (p : v₀ ~ v₁) (q : v₁ ~ v₂) → v₀ ~ v₂
  swap : (x y : X) (p : v₀ ~ v₁) → x ∷ y ∷ v₀ ~ y ∷ x ∷ v₁
  step : (x : X) (p : v₀ ~ v₁) → x ∷ v₀ ~ x ∷ v₁

instance
  ReflexivePerm : Reflexive (_~_ {X = X}{m})
  TransitivePerm : Transitive (_~_ {X = X}{m})
  SymmetricPerm : Symmetric (_~_ {X = X}{m})

refl' ⦃ ReflexivePerm ⦄ = refl

trans' ⦃ TransitivePerm ⦄ = trans

sym ⦃ SymmetricPerm ⦄ (refl v) = refl v
sym ⦃ SymmetricPerm ⦄ (trans p₁ p₂) = trans (sym p₂) (sym p₁)
sym ⦃ SymmetricPerm ⦄ (swap x y p) = swap y x (sym p)
sym ⦃ SymmetricPerm ⦄ (step x p) = step x (sym p)

open import Data.Vec.Property
open import Collection
open import Logic
open import Proof renaming (refl to refl')

∈-~ : ∀ (x : X){l l' : Vec X m}(p : l ~ l')
  → -------------------------
  x ∈ l ↔ x ∈ l'
∈-~ x p = go p , go $ sym p
  where go : ∀ {x : X}{l l' : Vec X m}(p : l ~ l')(q : x ∈ l) → x ∈ l'
        go (_~_.refl l) q = q
        go (_~_.trans p q) q' = go q $ go p q'
        go (swap {v₀ = v₀}{v₁} x y p) (x∈x∷ (y ∷ t)) = x∈tail y $ x∈x∷ v₁ 
        go (swap {v₀ = v₀}{v₁} x y p) (x∈tail x (x∈x∷ t)) = x∈x∷ (x ∷ v₁)
        go (swap x y p) (x∈tail x (x∈tail y q)) =
          x∈tail y $ x∈tail x $ go p q
        go (step {v₀ = v₀}{v₁} x p) (x∈x∷ t) = x∈x∷ v₁
        go (step x p) (x∈tail x' q) = x∈tail x' $ go p q

open import Proposition.Decidable
open import Data.Vec.Function

module Composable~ {m : ℕ}{X : 𝒰 ˙} where
  open TransMakeComposable (_~_ {X = X}{m}) public

remove-simp : ∀ x (v : Vec X m) p
  ⦃ dec== : HasDecidableIdentity X ⦄
  → -------------------------
  vec-remove x (x ∷ v) p == v
remove-simp x v p ⦃ dec== ⦄ with decide (x == x) ⦃ dec== ⦄
remove-simp x v p ⦃ dec== ⦄ | true p = Id.refl v
remove-simp x v p ⦃ dec== ⦄ | false ¬p =
  ⊥-recursion _ $ ¬p $ Id.refl x

remove-~-preserv : ∀ x {v v' : Vec X (m +1)} p
  ⦃ dec== : HasDecidableIdentity X ⦄
  (q : v ~ v')
  → ---------------------------------
  vec-remove x v p ~ vec-remove x v' (⟶ (∈-~ x q) p)
remove-~-preserv x p (refl v) = refl (vec-remove x v p)
remove-~-preserv x p (trans {v₀ = v₀}{v₁}{v₂} q q') =
  proof vec-remove x v₀ p
    〉 _~_ 〉 vec-remove x v₁ _
      :by: remove-~-preserv x p q
    〉 _~_ 〉 vec-remove x v₂ _
      :by: remove-~-preserv x (⟶ (∈-~ x q) p) q'
  qed
remove-~-preserv x p ⦃ dec== ⦄ (swap x' y' q)
  with decide (x' == x) ⦃ dec== ⦄
remove-~-preserv x p ⦃ dec== ⦄ (swap x y' q)
  | true (Id.refl x) with decide (y' == x) ⦃ dec== ⦄
remove-~-preserv x p ⦃ dec== ⦄ (swap x x q)
  | true (Id.refl x) | true (Id.refl x) = step x q
remove-~-preserv x p ⦃ dec== ⦄ (swap {v₀ = v₀}{v₁} x y' q)
  | true (Id.refl x) | false ¬p = step y' (
    proof v₀
      〉 _~_ 〉 v₁ :by: q
      〉 _==_ 〉 vec-remove x (x ∷ v₁) _
        :by: sym $ remove-simp x v₁ _
    qed)
remove-~-preserv x p ⦃ dec== ⦄ (swap {v₀ = v₀}{v₁} x' y' q)
  | false ¬p with decide (y' == x) ⦃ dec== ⦄
remove-~-preserv x p ⦃ dec== ⦄ (swap {v₀ = v₀}{v₁} x' x q)
  | false ¬p | true (Id.refl x) = step x' q
remove-~-preserv x (x∈x∷ (y' ∷ _)) ⦃ dec== ⦄ (swap x y' q)
  | false ¬p | false ¬p₁ = ⊥-recursion _ $ ¬p $ Id.refl x
remove-~-preserv x (x∈tail x' (x∈x∷ t)) ⦃ dec== ⦄ (swap x' x q)
  | false ¬p | false ¬p₁ = ⊥-recursion _ $ ¬p₁ $ Id.refl x
remove-~-preserv x (x∈tail x' (x∈tail y' p)) ⦃ dec== ⦄ (swap x' y' q)
  | false ¬p | false ¬p₁ with decide (x' == x) ⦃ dec== ⦄
remove-~-preserv x (x∈tail x' (x∈tail y' p)) ⦃ dec== ⦄ (swap x' y' q)
  | false ¬p₀ | false ¬p₁ | true p₀ = ⊥-recursion _ $ ¬p₀ p₀
remove-~-preserv x (x∈tail x' (x∈tail y' p)) ⦃ dec== ⦄
  (swap {v₀ = h ∷ v₀} x' y' q) | false ¬p | false ¬p₁ | false ¬p₂ =
  swap x' y' $ remove-~-preserv x p q
remove-~-preserv x p ⦃ dec== ⦄ (step x' q) with decide (x' == x) ⦃ dec== ⦄
remove-~-preserv x p ⦃ dec== ⦄ (step x' q) | true _ = q
remove-~-preserv x (x∈x∷ t) ⦃ dec== ⦄ (step x q) | false ¬p =
  ⊥-recursion _ $ ¬p $ Id.refl x
remove-~-preserv {m = m +1} x (x∈tail x' p) ⦃ dec== ⦄ (step x' q) | false ¬p =
  step x' (remove-~-preserv x p q)

vec-remove~ : ∀ h (t : Vec X m) v p
  ⦃ dec== : HasDecidableIdentity X ⦄
  → ------------------------------
  h ∷ t ~ v ↔ t ~ vec-remove h v p
⟶ (vec-remove~ h t (h ∷ t) p ⦃ dec== ⦄) (refl (h ∷ t))
  with decide (h == h) ⦃ dec== ⦄
⟶ (vec-remove~ h t (h ∷ t) p ⦃ dec== ⦄) (refl .(h ∷ t)) | true _ =
  refl t
⟶ (vec-remove~ h t (h ∷ t) p ⦃ dec== ⦄) (refl .(h ∷ t)) | false ¬h==h =
  ⊥-recursion _ $ ¬h==h $ refl' h
⟶ (vec-remove~ h t v p) (trans {v₀}{v₁}{v₂} p₁ p₂) =
  proof t
    〉 _~_ 〉 vec-remove h v₂ _
      :by: ⟶ (vec-remove~ h t v₂ $ ⟶ (∈-~ h p₁) (x∈x∷ t)) p₁
    〉 _~_ 〉 vec-remove h v p
      :by: {!!}
  qed
⟶ (vec-remove~ h .(y ∷ _) .(y ∷ h ∷ _) p) (swap .h y p₁) = {!!}
⟶ (vec-remove~ h t .(h ∷ _) p) (step .h p₁) = {!!}
⟵ (vec-remove~ h t v p) = {!!}
