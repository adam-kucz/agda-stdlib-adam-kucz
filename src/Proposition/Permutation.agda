{-# OPTIONS --safe --exact-split --prop  #-}
module Proposition.Permutation where

open import PropUniverses
open import Data.List
open import Relation.Binary
  renaming (refl to refl'; trans to trans')

private
  variable
    x y : X
    l l₁ l₂ l₃ : List X

data Perm {X : 𝒰 ˙} : Rel 𝒰 (List X) (List X) where
  refl : (l : List X) → Perm l l
  trans : (p : Perm l₁ l₂) (q : Perm l₂ l₃) → Perm l₁ l₃
  swap : (x y : X) (p : Perm l₁ l₂) → Perm (x ∷ y ∷ l₁) (y ∷ x ∷ l₂)
  step : (x : X) (p : Perm l₁ l₂) → Perm (x ∷ l₁) (x ∷ l₂)

instance
  ReflexivePerm : Reflexive (Perm {X = X})
  refl' ⦃ ReflexivePerm ⦄ = refl

  TransitivePerm : Transitive (Perm {X = X})
  trans' ⦃ TransitivePerm ⦄ = trans

  SymmetricPerm : Symmetric (Perm {X = X})
  sym ⦃ SymmetricPerm ⦄ (refl l) = refl l
  sym ⦃ SymmetricPerm ⦄ (trans p₁ p₂) = trans (sym p₂) (sym p₁)
  sym ⦃ SymmetricPerm ⦄ (swap x y p) = swap y x (sym p)
  sym ⦃ SymmetricPerm ⦄ (step x p) = step x (sym p)
