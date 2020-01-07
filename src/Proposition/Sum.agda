{-# OPTIONS --exact-split --safe --prop #-}
module Proposition.Sum where

open import PropUniverses

infixl 11 _,_
record Σₚ {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ˙ where
  constructor _,_
  field
    elem : X
    prop : 𝐴 elem

open Σₚ public

open import Proposition.Identity.Definition

Σₚ== :
  {𝐴 : (x : X) → 𝒰 ᵖ}
  {σ ρ : Σₚ 𝐴}
  (p : elem σ == elem ρ)
  → ------------------
  σ == ρ
Σₚ== {σ = σ} (refl _) = refl σ

from-Σₚ== : 
  {𝐴 : (x : X) → 𝒰 ᵖ}
  {σ ρ : Σₚ 𝐴}
  (p : σ == ρ)
  → ------------------
  elem σ == elem ρ
from-Σₚ== (refl σ) = refl (elem σ)

data ∃ {X : 𝒰 ˙} (𝐴 : (x : X) → 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  _,_ : (elem : X) (p : 𝐴 elem) → ∃ 𝐴

infixl 17 _∧_
record _∧_ (𝑋 : 𝒰 ᵖ) (𝑌 : 𝒱 ᵖ) : 𝒰 ⊔ 𝒱 ᵖ where
  constructor _,_
  field
    left : 𝑋
    right : 𝑌 

open _∧_ public
