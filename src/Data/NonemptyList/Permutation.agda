{-# OPTIONS --safe --exact-split --prop  #-}
module Data.NonemptyList.Permutation where

open import Data.NonemptyList.Definition

open import PropUniverses
open import Relation.Binary
  renaming (refl to refl'; trans to trans')
  hiding (_~_)

private
  variable
    x y : X
    l l₁ l₂ l₃ : NonemptyList X

data _~_ {X : 𝒰 ˙} : BinRel 𝒰 (NonemptyList X) where
  refl : (l : NonemptyList X) → l ~ l
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

open import Data.NonemptyList.Property
open import Collection
open import Logic
open import Proof

∈-~ : ∀ (x : X){l l'}(p : l ~ l')
  → -------------------------
  x ∈ l ↔ x ∈ l'
∈-~ x p = go p , go $ sym p
  where go : ∀ {l l'}(p : l ~ l')(q : x ∈ l) → x ∈ l'
        go (_~_.refl l) q = q
        go (_~_.trans p q) q' = go q $ go p q'
        go (swap {l} {l'} x y p) (x ∈head (y ∷ l)) =
          x ∈⦅ y ∷ x ∈head l' ⦆
        go (swap {.t} {l'} x' .x p) (x ∈⦅ x' ∷ x ∈head t ⦆) =
          x ∈head (x' ∷ l')
        go (swap {l} {l'} x' y p) (x ∈⦅ x' ∷ x ∈⦅ y ∷ q ⦆ ⦆) =
          x ∈⦅ y ∷ x ∈⦅ x' ∷ go p q ⦆ ⦆
        go (step {.t} {l'} x p) (x ∈head t) = x ∈head l'
        go (step {l} {l'} x' p) (x ∈⦅ x' ∷ q ⦆) = x ∈⦅ x' ∷ go p q ⦆
