{-# OPTIONS --safe --exact-split --prop  #-}
module Proposition.Permutation.Definition where

open import PropUniverses
open import Data.List
open import Relation.Binary
  renaming (refl to refl'; trans to trans')
  using (Rel; Reflexive; Transitive; Symmetric; sym)

private
  variable
    x y : X
    l l₁ l₂ l₃ : List X

data _~_ {X : 𝒰 ˙} : Rel 𝒰 (List X) (List X) where
  refl : (l : List X) → l ~ l
  trans : (p : l₁ ~ l₂) (q : l₂ ~ l₃) → l₁ ~ l₃
  swap : (x y : X) (p : l₁ ~ l₂) → x ∷ y ∷ l₁ ~ y ∷ x ∷ l₂
  step : (x : X) (p : l₁ ~ l₂) → x ∷ l₁ ~ x ∷ l₂

instance
  ReflexivePerm : Reflexive (_~_ {X = X})
  TransitivePerm : Transitive (_~_ {X = X})
  SymmetricPerm : Symmetric (_~_ {X = X})

refl' ⦃ ReflexivePerm ⦄ = refl

trans' ⦃ TransitivePerm ⦄ = trans

sym ⦃ SymmetricPerm ⦄ (refl l) = refl l
sym ⦃ SymmetricPerm ⦄ (trans p₁ p₂) = trans (sym p₂) (sym p₁)
sym ⦃ SymmetricPerm ⦄ (swap x y p) = swap y x (sym p)
sym ⦃ SymmetricPerm ⦄ (step x p) = step x (sym p)

