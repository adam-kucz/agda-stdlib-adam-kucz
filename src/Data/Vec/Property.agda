{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Property where

open import Data.Vec.Definition

open import PropUniverses
open import Logic
open import Proof

open import Data.Nat

data member {X : 𝒰 ˙} (x : X) : {n : ℕ} (l : Vec X n) → 𝒰₀ ᵖ where
  x∈x∷_ : ∀ {n} (t : Vec X n) → member x (x ∷ t)
  x∈tail : ∀ {n} (h : X) {t : Vec X n} (p : member x t) → member x (h ∷ t)

open import Collection hiding (_++_)

instance
  VecCollection : ∀ {X : 𝒰 ˙}{m} → Collection 𝒰₀ (Vec X m) X
  VecEmpty : Empty (Vec X 0) X
  VecListable : ∀ {m} → Listable 𝒰₀ (Vec X m) X

_∈_ ⦃ VecCollection ⦄ x = member x

∈++ : ∀{m m'}{x : X}
  (v : Vec X m)
  (v' : Vec X m')
  → ----------------------------
  x ∈ v ++ v' ↔ x ∈ v ∨ x ∈ v'
⟶ (∈++ [] v') p = ∨right p
⟶ (∈++ (h ∷ v) v') (x∈x∷ .(v ++ v')) = ∨left $ x∈x∷ v
⟶ (∈++ (h ∷ v) v') (x∈tail h p) with ⟶ (∈++ v v') p
⟶ (∈++ (h ∷ v) v') (x∈tail h p) | ∨left q = ∨left $ x∈tail h q
⟶ (∈++ (h ∷ v) v') (x∈tail h p) | ∨right q = ∨right q
⟵ (∈++ (_ ∷ t) v') (∨left (x∈x∷ t)) = x∈x∷ (t ++ v')
⟵ (∈++ (h ∷ t) v') (∨left (x∈tail h p)) = x∈tail h $ ⟵ (∈++ t v') $ ∨left p
⟵ (∈++ [] v') (∨right q) = q
⟵ (∈++ (h ∷ v) v') (∨right q) = x∈tail h $ ⟵ (∈++ v v') $ ∨right q

∅ ⦃ VecEmpty ⦄ = []
_∉∅ ⦃ VecEmpty ⦄ _ ()

open import Data.List

collection ⦃ VecListable ⦄ = VecCollection
to-list ⦃ VecListable ⦄ [] = []
to-list ⦃ VecListable ⦄ (h ∷ S) = h ∷ to-list S
⟶ (to-list-valid ⦃ VecListable ⦄) (x∈x∷ t) =
  x∈x∷ to-list t 
⟶ (to-list-valid ⦃ VecListable ⦄) (x∈tail h p) =
  x∈tail h (⟶ to-list-valid p)
⟵ (to-list-valid ⦃ VecListable ⦄ {h ∷ S}) (x∈x∷ .(to-list S)) =
  x∈x∷ S
⟵ (to-list-valid ⦃ VecListable ⦄ {h ∷ S}) (x∈tail h q) =
  x∈tail h (⟵ to-list-valid q)

vec-to-list-len : (v : Vec X m) → len (to-list v) == m
vec-to-list-len [] = Id.refl 0
vec-to-list-len (h ∷ v) = ap suc (vec-to-list-len v)

open import Proposition.Decidable

instance
  DecidableVec∈ : ⦃ d : HasDecidableIdentity X ⦄
    → -------------------------------------------
    ∀{n}{x : X}{v : Vec X n} → Decidable (x ∈ v)

DecidableVec∈ {v = []} = false λ ()
DecidableVec∈ {x = x}{h ∷ v} with decide (x == h)
... | true p = true (Id.coe (ap (_∈ h ∷ v) $ sym p) $ x∈x∷ v)
... | false ¬p with DecidableVec∈ {x = x}{v}
... | true p = true (x∈tail h p)
... | false ¬p' = false λ { (x∈x∷ v) → ¬p $ Id.refl x
                          ; (x∈tail x p') → ¬p' p'}
