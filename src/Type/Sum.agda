{-# OPTIONS --exact-split --safe --prop #-}
module Type.Sum where

open import Universes

infix 51 _,_
record Σ {X : 𝒰 ˙} (A : (x : X) → 𝒱 ˙) : 𝒰 ⊔ 𝒱 ˙ where
  constructor _,_
  field
    pr₁ : X
    pr₂ : A pr₁

infix 57 _×_
_×_ : (X : 𝒰 ˙) (Y : 𝒱 ˙) → 𝒰 ⊔ 𝒱 ˙
X × Y = Σ λ (_ : X) → Y

open Σ public

open import Proposition.Identity

Σ== :
  {A : (x : X) → 𝒰 ˙}
  {σ ρ : Σ A}
  (p : pr₁ σ == pr₁ ρ)
  (q : pr₂ σ == pr₂ ρ)
  → ------------------
  σ == ρ
Σ== {σ = σ} (refl _) (refl _) = refl σ
