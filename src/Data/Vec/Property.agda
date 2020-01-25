{-# OPTIONS --safe --exact-split --prop  #-}
module Data.Vec.Property where

open import Data.Vec.Definition

open import PropUniverses
open import Proposition.Identity
open import Logic

open import Data.Nat using (ℕ)

data member {X : 𝒰 ˙} (x : X) : {n : ℕ} (l : Vec X n) → 𝒰 ᵖ where
  x∈x∷_ : ∀ {n} (t : Vec X n) → member x (x ∷ t)
  x∈tail : ∀ {n} (h : X) {t : Vec X n} (p : member x t) → member x (h ∷ t)

open import Data.Collection

instance
  VecCollection : ∀ {X : 𝒰 ˙}{m} → Collection 𝒰 (Vec X m) X
  _∈_ ⦃ VecCollection ⦄ x = member x

open import Data.List

instance
  VecListable : ∀ {m} → Listable (Vec X m) X
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
