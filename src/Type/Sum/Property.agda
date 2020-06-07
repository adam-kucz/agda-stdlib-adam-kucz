{-# OPTIONS --exact-split --safe --prop #-}
module Type.Sum.Property where

open import Universes
open import Type.Sum.Definition
open import Proof

Σ== :
  {A : (x : X) → 𝒰 ˙}
  {σ ρ : Σ A}
  (p : pr₁ σ == pr₁ ρ)
  (q : pr₂ σ Het.== pr₂ ρ)
  → ------------------
  σ == ρ
Σ== {σ = σ} (Id.refl _) (Het.refl _) = Id.refl σ

open import Proposition.Sum renaming (_,_ to _,,_)

from-Σ== :
  {σ ρ : Σ A}
  (p : σ == ρ)
  → ------------------
  pr₁ σ == pr₁ ρ ∧ pr₂ σ Het.== pr₂ ρ
from-Σ== (Id.refl σ) = Id.refl (pr₁ σ) ,, Het.refl (pr₂ σ)

open import Function

[id×id]~id : [ 𝑖𝑑 X × 𝑖𝑑 Y ] ~ id
[id×id]~id = Het.refl

〈pr₁,pr₂〉~id : 〈 pr₁ , pr₂ 〉 ~ 𝑖𝑑 (X × Y)
〈pr₁,pr₂〉~id = Het.refl
